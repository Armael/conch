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
    acc +
    match instr with
    | I (_, _) | Idat _ -> 1
    | Idat16 _ -> 2
    | Icomment _ -> 0
  ) 0 l

let rec alength = function
  | List l -> instr_list_len l
  | Append (l1, l2) -> alength l1 + alength l2

let rec aflatten = function
  | List l -> l
  | Append (l1, l2) -> List.append (aflatten l1) (aflatten l2)

let fail fmt =
  Printf.ksprintf (fun s -> failwith s) fmt

let sp_addr = 0
let mem_start_addr = 1

let init, alloc_offset =
  let setup (main_loc: int) (mem_start: int) =
    List [
      (* initialize sp, mem_start *)
      (* sp initially points to the end of the first page, i.e. 0xfe given that a
         stack slots is 2 bytes *)
      i LIT []; Idat 0xfe; i LIT []; Idat sp_addr; i STZ [];
      (* mem_start points to the rest of memory after the program *)
      i LIT [S]; Idat16 mem_start; i LIT []; Idat mem_start_addr; i STZ [S];
      (* jump to the main function *)
      i LIT [S]; Idat16 main_loc; i JMP [S];
      (* end of the program *)
      i BRK []
    ]
  in
  let alloc =
    List [
      (* alloc *)
      Icomment "alloc";
      i LIT []; Idat 0; (* pad mem_start_addr *) i LIT []; Idat mem_start_addr;
      i LDZ [S;K]; (* mem_start ; mem_start_addr ; alloc_sz *)
      i ROT [S]; (* alloc_sz ; mem_start ; mem_start_addr *)
      i ADD [S;K]; (* mem_start + alloc_sz ; alloc_sz ; mem_start ; mem_start_addr *)
      i NIP [S]; (* mem_start + alloc_sz ; mem_start ; mem_start_addr *)
      i ROT [S]; (* mem_start_addr ; mem_start + alloc_sz ; mem_start *)
      i NIP []; (* unpad mem_start_addr *)
      i STZ [S]; (* mem_start_addr <- mem_start + alloc_sz *)
      (* mem_start *)
      i JMP [S;R] (* ret *)
    ]
  in
  let init main_loc mem_start =
    setup main_loc mem_start ++ alloc
  in
  let alloc_offset = alength (setup 0 0) in
  init, alloc_offset

let prog_start = 0x0100
let alloc_addr = prog_start + alloc_offset

(*
let init (main_loc: int) =
  [
    (* jump to the main function *)
    (*  0 *) ICall main_loc;
    (* end of the program: return to exit 0 *)
    (*  1 *) IConst (RDI, 0L);
    (*  2 *) IExit;
    (* alloc *)
    (*  3 *) IComment "alloc";
    (* XXX: somewhat awkward register handling because of the awkward
       condition/conditional jumps *)
    (*  4 *) IMov (RDX, R14);
    (*  5 *) IAdd (R14, RAX);
    (*  6 *) ILt (R14, R15);
    (*  7 *) IJump (CIfFalse RAX, 11);
    (*  8 *) IMov (RAX, RDX);
    (*  9 *) IRet;
    (* give up *)
    (* 10 *) IComment "exit 1";
    (* 11 *) IConst (RDI, 1L);
    (* 12 *) IExit;
  ]
*)

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
    i LIT []; Idat sp_addr;
    i LDZ [];  (* read sp *)
    Idat k; i ADD []; (* sp+k *)
  ]

(* push the value at the top of the vm stack
   to the top of the C stack
*)
let push_to_c_stack =
  List [
    i LIT []; Idat sp_addr; i LDZ [K]; i LIT []; Idat 1; i SUB []; (* sp-1 *)
    i SWP []; i STZ [K]; i POP []; (* write the new sp (sp-1) *)
    i STZ [S];
  ]

(* decrease SP by k *)
let sub_sp (k: int) =
  List [
    i LIT []; Idat sp_addr; i LDZ [K]; i LIT []; Idat k; i SUB []; (* sp-k *)
    i SWP []; i STZ []
  ]

(* increment SP by k *)
let add_sp (k: int) =
  List [
    i LIT []; Idat sp_addr; i LDZ [K]; i LIT []; Idat k; i ADD []; (* sp+k *)
    i SWP []; i STZ []
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
    List [i LDZ [S]] (* read sp+k as a 16 bits int *)

  let addr (v: ident) (stack: c_stack) =
    let k = find_local' v stack in
    List [i LIT []; Idat 0] ++ (* this pads the result to 16 bits *)
    get_stackelt_addr k

  let const16 (c: int) =
    assert (c land 0xFFFF = c);
    List [i LIT [S]; Idat16 c]

 (* /!\ arguments are passed in reverse on the stack *)
  let c_add = List [i ADD [S]]
  let c_sub = List [i SWP [S]]
  let c_div = List [i SWP [S]]
  let c_mul = List [i MUL [S]]
  let c_and = List [i AND [S]]
  let c_or = List [i ORA [S]]
  let c_xor = List [i EOR [S]]
  let c_cmp_lt = List [i LTH [S]; i LIT []; Idat 0; i SWP [] (* pad *)]
  let c_cmp_gt = List [i GTH [S]; i LIT []; Idat 0; i SWP [] (* pad *)]
  let c_cmp_eq = List [i EQU [S]; i LIT []; Idat 0; i SWP [] (* pad *)]
  let c_cmp_neq = List [i NEQ [S]; i LIT []; Idat 0; i SWP [] (* pad *)]

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
    get_stackelt_addr k ++
    Expr.expr stack e ++
    List [i STA []]

  let store (a: expr) (w: expr) (stack: c_stack) =
    Expr.exprs stack [a; w] ++
    List [i SWP [S]; i STA [S]]

  let call (lid: ident option) (target: int) (xs: expr list) stack =
    Expr.exprs stack xs ++
    call_pops (List.length xs) ++
    List [i LIT [S]; Idat16 target; i JSR [S]] ++
    (match lid with
     | None -> List []
     | Some v -> Expr.var v stack)

  let putchar =
    List [i LIT []; Idat 18; i DEO [S]]

  let malloc =
    List [i LIT [S]; Idat16 alloc_addr; i JSR [S]]

  let builtin (lid: ident option) (ef: external_function) (xs: expr list) stack =
    Expr.exprs stack xs ++
    call_pops (List.length xs) ++
    (match ef with
     | EF_putchar -> putchar
     | EF_malloc -> malloc
    ) ++
    (match lid with
     | None -> List []
     | Some v -> Expr.var v stack)

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
        i LIT [S]; Idat16 c1_loc; i JCN [S]
      ] ++
      c2 ++
      List [i LIT [S]; Idat16 end_loc; i JMP [S]] ++
      c2
    | Sloop (e, s) ->
      let ce = Expr.expr stack e in
      let c_loc = loc + alength ce + 9 in
      let c = stmt c_loc funcs stack s in
      let end_loc = loc + alength ce + 9 + alength c + 4 in
      ce ++
      List [
        (* cond: 16 bits -> 8 bits *) i ORA [];
        i LIT [S]; Idat16 c_loc; i JCN [S]
      ] ++
      List [i LIT [S]; Idat16 end_loc; i JMP [S]] ++
      c ++
      List [i LIT [S]; Idat16 loc; i JMP [S]]
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
  let (_, fs) = decs init_len [] p.prog_defs in
  let (c, _) = decs init_len fs p.prog_defs in
  let main_loc = lookup_fname p.prog_main fs in
  let mem_start = prog_start + init_len + alength c in
  aflatten (init main_loc mem_start ++ c)
