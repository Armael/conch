open Common
open Types
open Cminor
open Target

let die fmt = Common.die ~where:"codegen" fmt

type 'a applist =
  | List of 'a list
  | Append of 'a applist * 'a applist

let (++) l1 l2 = Append (l1, l2)

let appendl (l: 'a applist list): 'a applist =
  List.fold_left (++) (List []) l

let instr_list_len l =
  List.fold_left (fun acc instr ->
    acc + inst_size instr
  ) 0 l

let rec alength = function
  | List l -> instr_list_len l
  | Append (l1, l2) -> alength l1 + alength l2

let rec aflatten = function
  | List l -> l
  | Append (l1, l2) -> List.append (aflatten l1) (aflatten l2)

let szflag ty =
  match sizeof ty with
  | 1 -> []
  | 2 -> [S]
  | _ -> assert false

let ptrtype = function
  | Tptr ty -> ty
  | _ -> assert false

let globs_start = 0x0
let prog_start = 0x0100

let init, sp_addr, alloc_addr, init_end_offset =
  let setup (main_loc: int) =
    List [
      (* jump to the main function *)
      Idat16 main_loc; i JSR [S];
      (* end of the program *)
      i BRK [];
    ] in
  let localdata (mem_start: int) =
    List [ (* initial values for sp and heap_start *)
      (* stack size: 512 bytes *)
      (* sp initially points to the end of the stack, i.e. mem_start+0x200.keep
         allocating stack space means decrementing sp by the size required *)
      Idat16 (mem_start + 0x200);
      (* heap_start initially points to the part of memory after the stack *)
      Idat16 (mem_start + 0x200);
    ]
  in
  let sp_addr = prog_start + alength (setup 0) in
  let heap_start_addr = sp_addr + 2 in
  let alloc =
    List [
      (* alloc *)
      Icomment "alloc";
      Idat16 heap_start_addr;
      i LDA [S;K]; (* mem_start ; mem_start_addr ; alloc_sz *)
      i ROT [S]; (* alloc_sz ; mem_start ; mem_start_addr *)
      i ADD [S;K]; (* mem_start + alloc_sz ; alloc_sz ; mem_start ; mem_start_addr *)
      i NIP [S]; (* mem_start + alloc_sz ; mem_start ; mem_start_addr *)
      i ROT [S]; (* mem_start_addr ; mem_start + alloc_sz ; mem_start *)
      i STA [S]; (* mem_start_addr <- mem_start + alloc_sz *)
      (* mem_start *)
      i JMP [S;R] (* ret *)
    ]
  in
  let init main_loc mem_start =
    setup main_loc ++
    localdata mem_start ++
    alloc
  in
  let alloc_addr = prog_start + alength (setup 0 ++ localdata 0) in
  let init_end_offset = alength (init 0 0) in
  init, sp_addr, alloc_addr, init_end_offset

type c_stack = ident list

let find_local ty_ids (v: ident) (stack: c_stack): int =
  let rec loop i = function
    | [] -> assert false
    | v' :: vs ->
      if v = v' then i
      else loop (i + sizeof (IdentMap.find v' ty_ids)) vs
  in loop 0 stack

let stack_size ty_ids (stack: c_stack): int =
  List.fold_left (fun sz v ->
    sz + sizeof (IdentMap.find v ty_ids)
  ) 0 stack

(* k: offset in bytes *)
let get_stackelt_addr (k: int) =
  List [
    Idat16 sp_addr;
    i LDA [S];  (* read sp *)
    Idat16 k; i ADD [S]; (* sp+k *)
  ]

(* push the value at the top of the vm stack of type [ty]
   to the top of the C stack
*)
let push_to_c_stack ty =
  assert (sizeof ty <> 0);
  List [
    Idat16 sp_addr; i LDA [S;K]; Idat16 (sizeof ty); i SUB [S]; (* sp-sizeof(ty) *)
    i SWP [S]; i STA [S;K]; i POP [S]; (* write the new sp (sp-sizeof(ty)) *)
    i STA (szflag ty); (* write the value at the top of the stack *)
  ]

(* decrease SP by k bytes *)
let sub_sp (k: int) =
  if k = 0 then List [] else
    List [
      Idat16 sp_addr; i LDA [S;K]; Idat16 k; i SUB [S]; (* sp-k *)
      i SWP [S]; i STA [S]
    ]

(* increment SP by k bytes *)
let add_sp (k: int) =
  if k = 0 then List [] else
    List [
      Idat16 sp_addr; i LDA [S;K]; Idat16 k; i ADD [S]; (* sp+k *)
      i SWP [S]; i STA [S]
    ]

module Expr = struct
  (* invariant:
     top of the vm stack = result of evaluating last expression
     vm stack = temporaries
     c stack = variables and locals

     an expression (fragment) operates on the vm stack:
     - takes its arguments from the vm stack
     - writes its result on top of the stack
  *)

  let var idents_ty (v: ident) (stack: c_stack) =
    let k = find_local idents_ty v stack in
    get_stackelt_addr k ++
    List [i LDA (szflag (IdentMap.find v idents_ty))] (* read sp+k *)

  let glob (off: int) ty =
    let glob_addr = globs_start + off in
    List [Idat glob_addr; i LDZ (szflag ty)]

  let addr idents_ty (v: ident) (stack: c_stack) =
    let k = find_local idents_ty v stack in
    get_stackelt_addr k

  let const16 (c: int) =
    assert (c land 0xFFFF = c);
    List [Idat16 c]

  let const8 (c: int) =
    assert (c land 0xFF = c);
    List [Idat c]

 (* /!\ arguments are passed in reverse on the stack:
    the second argument is on top of the stack *)
  let c_binop ty1 ty2 = function
    | Oadd ->
      begin match ty1, ty2 with
      | Tptr pty, ty -> (* pointer + int *)
        List (if sizeof ty = 1 then [Idat 0; i SWP [] (* pad to 16 bits *)]
              else []) ++
        List (if sizeof pty > 1 then [Idat16 (sizeof pty); i MUL [S]] else []) ++
        List [i ADD [S]]
      | ty, Tptr pty -> (* int + pointer *)
        if sizeof ty1 = 2 && sizeof pty <= 1 then
          List [i ADD [S]]
        else
          List (if sizeof ty = 1 then [Idat 0; i ROT []; i ROT []] else []) ++
          List [i SWP [S]] ++
          List (if sizeof ty = 1 then [i SWP []] else []) ++
          List (if sizeof pty > 1 then [Idat16 (sizeof pty); i MUL [S]] else []) ++
          List [i ADD [S]]
      | Tbase _, Tbase _ ->
        List [i ADD (szflag ty1)]
      end
    | Osub ->
      begin match ty1, ty2 with
      | Tptr _, Tptr _ -> (* ptr - ptr; result in bytes as a int16 *)
        List [i SUB [S]]
      | Tptr pty, ty -> (* ptr - int *)
        List (if sizeof ty = 1 then [Idat 0; i SWP [] (* pad to 16 bits *)]
              else []) ++
        List (if sizeof pty > 1 then [Idat16 (sizeof pty); i MUL [S]] else []) ++
        List [i SUB [S]]
      | Tbase _, Tbase _ ->
        List [i SUB (szflag ty1)]
      | _, _ ->
        assert false
      end
    | Odiv -> List [i DIV (szflag ty1)]
    | Omul -> List [i MUL (szflag ty1)]
    | Oand -> List [i AND (szflag ty1)]
    | Oor -> List [i ORA (szflag ty1)]
    | Oxor -> List [i EOR (szflag ty1)]
    | Ocmp Lt -> List [i LTH (szflag ty1)]
    | Ocmp Gt -> List [i GTH (szflag ty1)]
    | Ocmp Eq -> List [i EQU (szflag ty1)]
    | Ocmp Neq -> List [i NEQ (szflag ty1)]

  let c_load ty =
    List [i LDA (szflag (ptrtype ty))]

  let c_cast ty1 ty2 =
    match ty1, ty2 with
    | Tbase Tvoid, _ | _, Tbase Tvoid -> assert false
    | Tptr _, Tptr _ -> List []
    | Tbase Tint8, (Tbase Tint16 | Tptr _) -> List [Idat 0; i SWP []] (* pad *)
    | (Tbase Tint16 | Tptr _), Tbase Tint8 -> List [i NIP []] (* drop higher byte *)
    | Tbase Tint8, Tbase Tint8
    | (Tbase Tint16 | Tptr _), (Tbase Tint16 | Tptr _) -> List []

  let rec expr idents_ty (stack: c_stack) (e: expr) =
    match fst e with
    | Evar v -> var idents_ty v stack
    | Eglob n -> glob n (type_of_expr e)
    | Eaddr v -> addr idents_ty v stack
    | Econst (C8 x) -> const8 x
    | Econst (C16 x) -> const16 x
    | Ebinop (op, e1, e2) ->
      exprs idents_ty stack [e1; e2] ++
      c_binop (type_of_expr e1) (type_of_expr e2) op
    | Eload e -> expr idents_ty stack e ++ c_load (type_of_expr e)
    | Ecast (e, to_ty) ->
      expr idents_ty stack e ++ c_cast (type_of_expr e) to_ty

  and exprs idents_ty (stack: c_stack) = function
    | [] -> List []
    | [e] -> expr idents_ty stack e
    | e :: es -> expr idents_ty stack e ++ exprs_aux idents_ty stack es

  and exprs_aux idents_ty (stack: c_stack) = function
    | [] -> List []
    | e :: es ->
      expr idents_ty stack e ++
      exprs_aux idents_ty stack es
end

let call_pops (tys: ty list) =
  appendl (List.map (fun ty -> push_to_c_stack ty) tys)

let rec lookup_fname (f: ident) (funcs: (ident * int) list): int =
  match funcs with
  | [] -> 0 (* dummy *)
  | (f', a) :: fs -> if f = f' then a else lookup_fname f fs

module Stmt = struct
  let skip = List []

  let assign idents_ty (v: ident) (e: expr) (stack: c_stack) =
    let k = find_local idents_ty v stack in
    Expr.expr idents_ty stack e ++
    get_stackelt_addr k ++
    List [i STA (szflag (IdentMap.find v idents_ty))]

  let assign_glob idents_ty (off: int) (e: expr) (stack: c_stack) =
    let glob_addr = globs_start + off in
    Expr.expr idents_ty stack e ++
    List [Idat glob_addr; i STZ (szflag (type_of_expr e))]

  let store idents_ty (a: expr) (w: expr) (stack: c_stack) =
    Expr.exprs idents_ty stack [w; a] ++
    List [i STA (szflag (type_of_expr w))]

  let call idents_ty (lid: ident option) (target: int) (xs: expr list) stack =
    Expr.exprs idents_ty stack xs ++
    call_pops (List.rev_map type_of_expr xs) ++
    List [Idat16 target; i JSR [S]] ++
    (match lid with
     | None -> List []
     | Some v ->
       let k = find_local idents_ty v stack in
       get_stackelt_addr k ++ List [i STA (szflag (IdentMap.find v idents_ty))])

  let ef_putchar =
    List [Idat 0x18; i DEO []]

  let ef_malloc args_ty =
    begin match args_ty with
    | [Tbase Tint16] -> List []
    | [Tbase Tint8] -> List [Idat 0; i SWP []] (* pad *)
    | _ -> assert false
    end ++
    List [Idat16 alloc_addr; i JSR [S]]

  let ef_out args_ty =
    match args_ty with
    | [ty; _] -> List [i DEO (szflag ty)]
    | _ -> assert false

  let ef_in8 =
    List [i DEI []]

  let ef_in16 =
    List [i DEI [S]]

  (* let type_of_retid_opt ty_idents id_opt =
   *   (Option.fold
   *      ~none:(Tbase Tvoid)
   *      ~some:(fun v -> IdentMap.find v ty_idents)
   *      id_opt) *)

  let builtin idents_ty (lid: ident option) (ef: external_function) (xs: expr list) stack =
    let args_ty = List.map snd xs in
    Expr.exprs idents_ty stack xs ++
    (match ef with
     | EF_putchar -> ef_putchar
     | EF_malloc -> ef_malloc args_ty
     | EF_out -> ef_out args_ty
     | EF_in8 -> ef_in8
     | EF_in16 -> ef_in16
    ) ++
    (match lid with
     | None -> List []
     | Some v ->
       let k = find_local idents_ty v stack in
       get_stackelt_addr k ++ List [i STA (szflag (IdentMap.find v idents_ty))])

  let rec stmt idents_ty (loc: int) (funcs: (ident * int) list) stack = function
    | Sskip -> skip
    | Sassign (v, e) -> assign idents_ty v e stack
    | Sassign_glob (off, e) -> assign_glob idents_ty off e stack
    | Sstore (a, w) -> store idents_ty a w stack
    | Scall (lid, f, xs) -> call idents_ty lid (lookup_fname f funcs) xs stack
    | Sbuiltin (lid, ef, xs) -> builtin idents_ty lid ef xs stack
    | Sseq (s1, s2) ->
      let c1 = stmt idents_ty loc funcs stack s1 in
      c1 ++ stmt idents_ty (loc + alength c1) funcs stack s2
    | Sifthenelse (e, s1, s2) ->
      let ce = Expr.expr idents_ty stack e in
      (* layout s2 before s1 *)
      let c2 = stmt idents_ty (loc + alength ce + 4) funcs stack s2 in
      let c1_loc = loc + alength ce + 4 + alength c2 + 4 in
      let c1 = stmt idents_ty c1_loc funcs stack s1 in
      let end_loc = loc + alength ce + 4 + alength c2 + 4 + alength c1 in
      ce ++
      List [Idat16 c1_loc; i JCN [S]] ++
      c2 ++
      List [Idat16 end_loc; i JMP [S]] ++
      c1
    | Sloop (e, s) ->
      let c_loc = loc + 4 in
      let c = stmt idents_ty c_loc funcs stack s in
      let ce_loc = loc + 4 + alength c in
      let ce = Expr.expr idents_ty stack e in
      List [Idat16 ce_loc; i JMP [S]] ++
      c ++
      ce ++
      List [Idat16 c_loc; i JCN [S]]
end

module Func = struct
  let func (loc: int) (funcs: (ident * int) list) (f: func) =
    let vars = List.map fst f.fn_vars in
    let stack = vars @ (List.map fst f.fn_params) in
    (* reserve stack space for the local variables *)
    let subsp = sub_sp (stack_size f.fn_lenv vars) in
    subsp ++
    Stmt.stmt f.fn_lenv (loc + alength subsp) funcs stack f.fn_body ++
    (match f.fn_ret with
     | None -> List []
     | Some rete -> Expr.expr f.fn_lenv stack rete) ++
    add_sp (stack_size f.fn_lenv stack) ++
    List [i JMP [S;R] (* ret *)]
end

let rec decs (loc: int) (funcs: (ident * int) list) (ds: (ident * func) list) =
  match ds with
  | [] -> (List [], [])
  | (fv, f) :: ds ->
    let c = Func.func loc funcs f in
    let (cs, fs) = decs (loc + alength c) funcs ds in
    (List [Icomment fv] ++ c ++ cs, (fv, loc) :: fs)

let program (p: program) =
  let init_len = alength (init 0 0 (* dummys *)) in
  let loc0 = prog_start + init_len in
  let (_, fs) = decs loc0 [] p.prog_defs in
  let (c, _) = decs loc0 fs p.prog_defs in
  let main_loc = lookup_fname p.prog_main fs in
  let mem_start = prog_start + init_len + alength c in
  aflatten (init main_loc mem_start ++ c)
