open Cminor
open Target

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

let fail fmt =
  Printf.ksprintf (fun s -> failwith s) fmt

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
      (* sp initially points to the end of the first page, i.e. mem_start+0x1fe
         given that a stack slots is 2 bytes *)
      Idat16 (mem_start + 0x1fe);
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

let find_local (v: ident) (stack: c_stack): int option =
  let rec loop i = function
    | [] -> None
    | v' :: vs -> if v = v' then Some i else loop (i+1) vs
  in loop 0 stack

let find_local' (v: ident) (stack: c_stack): int =
  match find_local v stack with
  | None -> fail "Unbound local variable %s" v
  | Some k -> k


let get_stackelt_addr (k: int) =
  List [
    Idat16 sp_addr;
    i LDA [S];  (* read sp *)
    Idat16 (2*k); i ADD [S]; (* sp+2*k *) (* 1 stack slot = 2 bytes *)
  ]

(* push the value at the top of the vm stack
   to the top of the C stack
*)
let push_to_c_stack =
  List [
    Idat16 sp_addr; i LDA [S;K]; Idat16 2; i SUB [S]; (* sp-2 *)
    i SWP [S]; i STA [S;K]; i POP [S]; (* write the new sp (sp-2) *)
    i STA [S];
  ]

(* decrease SP by k slots *)
let sub_sp (k: int) =
  List [
    Idat16 sp_addr; i LDA [S;K]; Idat16 (2*k); i SUB [S]; (* sp-2*k *) (* 1 slot = 2 bytes *)
    i SWP [S]; i STA [S]
  ]

(* increment SP by k slots *)
let add_sp (k: int) =
  List [
    Idat16 sp_addr; i LDA [S;K]; Idat16 (2*k); i ADD [S]; (* sp+2*k *)
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

  let var (v: ident) (stack: c_stack) =
    let k = find_local' v stack in
    get_stackelt_addr k ++
    List [i LDA [S]] (* read sp+k *)

  let addr (v: ident) (stack: c_stack) =
    let k = find_local' v stack in
    get_stackelt_addr k

  let const16 (c: int) =
    assert (c land 0xFFFF = c);
    List [Idat16 c]

 (* /!\ arguments are passed in reverse on the stack *)
  let c_add = List [i ADD [S]]
  let c_sub = List [i SUB [S]]
  let c_div = List [i DIV [S]]
  let c_mul = List [i MUL [S]]
  let c_and = List [i AND [S]]
  let c_or = List [i ORA [S]]
  let c_xor = List [i EOR [S]]
  let c_cmp_lt = List [i LTH [S]; Idat 0; i SWP [] (* pad *)]
  let c_cmp_gt = List [i GTH [S]; Idat 0; i SWP [] (* pad *)]
  let c_cmp_eq = List [i EQU [S]; Idat 0; i SWP [] (* pad *)]
  let c_cmp_neq = List [i NEQ [S]; Idat 0; i SWP [] (* pad *)]

  let c_binop = function
    | Oadd -> c_add
    | Osub -> c_sub
    | Odiv -> c_div
    | Omul -> c_mul
    | Oand -> c_and
    | Oor -> c_or
    | Oxor -> c_xor
    | Ocmp Lt -> c_cmp_lt
    | Ocmp Gt -> c_cmp_lt
    | Ocmp Eq -> c_cmp_eq
    | Ocmp Neq -> c_cmp_neq

  let c_load =
    List [i LDA [S]]

  let rec expr (stack: c_stack) = function
    | Evar v -> var v stack
    | Eaddr v -> addr v stack
    | Econst c -> const16 c
    | Ebinop (op, e1, e2) ->
      exprs stack [e1; e2] ++ c_binop op
    | Eload e -> expr stack e ++ c_load

  and exprs (stack: c_stack) = function
    | [] -> List []
    | [e] -> expr stack e
    | e :: es -> expr stack e ++ exprs_aux stack es

  and exprs_aux (stack: c_stack) = function
    | [] -> List []
    | e :: es ->
      expr stack e ++
      exprs_aux stack es
end

let call_pops (k: int) =
  appendl (List.init k (fun _ -> push_to_c_stack))

let rec lookup_fname (f: ident) (funcs: (ident * int) list): int =
  match funcs with
  | [] -> 0 (* dummy *)
  | (f', a) :: fs -> if f = f' then a else lookup_fname f fs

module Stmt = struct
  let skip = List []

  let assign (v: ident) (e: expr) (stack: c_stack) =
    let k = find_local' v stack in
    Expr.expr stack e ++
    get_stackelt_addr k ++
    List [i STA [S]]

  let store (a: expr) (w: expr) (stack: c_stack) =
    Expr.exprs stack [w; a] ++
    List [i STA [S]]

  let call (lid: ident option) (target: int) (xs: expr list) stack =
    Expr.exprs stack xs ++
    call_pops (List.length xs) ++
    List [Idat16 target; i JSR [S]] ++
    (match lid with
     | None -> List []
     | Some v ->
       let k = find_local' v stack in
       get_stackelt_addr k ++ List [i STA [S]])

  let putchar =
    List [Idat 0x18; i DEO [S]]

  let malloc =
    List [Idat16 alloc_addr; i JSR [S]]

  let builtin (lid: ident option) (ef: external_function) (xs: expr list) stack =
    Expr.exprs stack xs ++
    (match ef with
     | EF_putchar -> putchar
     | EF_malloc -> malloc
    ) ++
    (match lid with
     | None -> List []
     | Some v ->
       let k = find_local' v stack in
       get_stackelt_addr k ++ List [i STA [S]])

  let rec stmt (loc: int) (funcs: (ident * int) list) stack = function
    | Sskip -> skip
    | Sassign (v, e) -> assign v e stack
    | Sstore (a, w) -> store a w stack
    | Scall (lid, f, xs) -> call lid (lookup_fname f funcs) xs stack
    | Sbuiltin (lid, ef, xs) -> builtin lid ef xs stack
    | Sseq (s1, s2) ->
      let c1 = stmt loc funcs stack s1 in
      c1 ++ stmt (loc + alength c1) funcs stack s2
    | Sifthenelse (e, s1, s2) ->
      let ce = Expr.expr stack e in
      (* layout s2 before s1 *)
      let c2 = stmt (loc + alength ce + 5) funcs stack s2 in
      let c1_loc = loc + alength ce + 5 + alength c2 + 4 in
      let c1 = stmt c1_loc funcs stack s1 in
      let end_loc = loc + alength ce + 5 + alength c2 + 4 + alength c1 in
      ce ++
      List [
        (* condition: 16 bits -> 8 bits *) i ORA [];
        Idat16 c1_loc; i JCN [S]
      ] ++
      c2 ++
      List [Idat16 end_loc; i JMP [S]] ++
      c1
    | Sloop (e, s) ->
      let ce = Expr.expr stack e in
      let c_loc = loc + alength ce + 9 in
      let c = stmt c_loc funcs stack s in
      let end_loc = loc + alength ce + 9 + alength c + 4 in
      ce ++
      List [
        (* cond: 16 bits -> 8 bits *) i ORA [];
        Idat16 c_loc; i JCN [S]
      ] ++
      List [Idat16 end_loc; i JMP [S]] ++
      c ++
      List [Idat16 loc; i JMP [S]]
end

module Func = struct
  let func (loc: int) (funcs: (ident * int) list) (f: func) =
    let stack = f.fn_vars @ f.fn_params in
    let subsp = sub_sp (List.length f.fn_vars) in (* reserve stack space for the local variables *)
    subsp ++
    Stmt.stmt (loc + alength subsp) funcs stack f.fn_body ++
    (match f.fn_ret with
     | None -> List []
     | Some rete -> Expr.expr stack rete) ++
    add_sp (List.length f.fn_vars + List.length f.fn_params) ++
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
