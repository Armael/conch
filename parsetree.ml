type comparison =
  | Lt
  | Gt
  | Eq
  | Neq

type binary_op =
  | Oadd
  | Osub
  | Odiv
  | Omul
  | Oand
  | Oor
  | Oxor
  | Ocmp of comparison

type ident = string

type tybase = Tvoid | Tint8 | Tint16
type ty =
  | Tbase of tybase
  | Tptr of ty

type const =
  | C8 of int
  | C16 of int

type expr =
  | Evar of ident
  | Eaddr of ident
  | Econst of const
  | Ebinop of binary_op * expr * expr
  | Eload of expr
  | Ecast of expr * ty

type external_function =
  | EF_putchar
  | EF_malloc

type 'expr stmt' =
  | Sskip
  | Sassign of ident * 'expr
  | Sstore of 'expr * 'expr
  | Scall of ident option * ident * 'expr list
  | Sbuiltin of ident option * external_function * 'expr list
  | Sseq of 'expr stmt' * 'expr stmt'
  | Sifthenelse of 'expr * 'expr stmt' * 'expr stmt'
  | Sloop of 'expr * 'expr stmt'

type stmt = expr stmt'

type func = {
  fn_params : (ident * ty) list;
  fn_vars : (ident * ty) list;
  fn_body : stmt;
  fn_ret : expr option;
  fn_ret_ty : ty;
}

type program = {
  prog_defs : (ident * func) list;
  prog_main : ident;
}

module IdentMap : Map.S with type key := ident = Map.Make(String)

(* printing *)

let pp_tybase fmt = function
  | Tvoid -> Format.fprintf fmt "void"
  | Tint8 -> Format.fprintf fmt "u8"
  | Tint16 -> Format.fprintf fmt "u16"

let rec pp_ty fmt = function
  | Tbase ty -> pp_tybase fmt ty
  | Tptr ty -> Format.fprintf fmt "*%a" pp_ty ty

let pp_ty fmt ty = pp_ty fmt ty

let string_of_op = function
  | Oadd -> "+"
  | Osub -> "-"
  | Odiv -> "/"
  | Omul -> "*"
  | Oand -> "and"
  | Oor -> "or"
  | Oxor -> "xor"
  | Ocmp Lt -> "<"
  | Ocmp Gt -> ">"
  | Ocmp Eq -> "="
  | Ocmp Neq -> "!="

let rec pp_expr fmt = function
  | Evar v -> Format.fprintf fmt "%s" v
  | Eaddr v -> Format.fprintf fmt "(& %s)" v
  | Econst (C8 x) -> Format.fprintf fmt "%d" x
  | Econst (C16 x) -> Format.fprintf fmt "#%d" x
  | Ebinop (op, e1, e2) ->
    Format.fprintf fmt "(%a %s %a)" pp_expr e1 (string_of_op op) pp_expr e2
  | Eload e -> Format.fprintf fmt "(* %a)" pp_expr e
  | Ecast (e, ty) -> Format.fprintf fmt "(%a as %a)" pp_expr e pp_ty ty

let string_of_builtin = function
  | EF_putchar -> "putchar"
  | EF_malloc -> "malloc"

(* parsing: from sexps *)

let die fmt = Common.die ~where:"parsing" fmt

let strtl s = String.sub s 1 (String.length s - 1)

let ty_of_string str =
  let rec aux s =
    if Char.equal s.[0] '*' then Tptr (aux (strtl s))
    else if String.equal s "void" then Tbase Tvoid
    else if String.equal s "u8" then Tbase Tint8
    else if String.equal s "u16" then Tbase Tint16
    else die "cannot parse type %s" str
  in
  if Char.equal str.[0] ':' then aux (strtl str)
  else die "cannot parse type %s" str

let typed_idents_of_sexps s =
  let strings =
    List.map (function `Atom s -> s | `List _ -> die "expected an identifier or a type name") s in
  let rec loop = function
  | ty :: ident :: rest -> (ident, ty_of_string ty) :: loop rest
  | [] -> []
  | [_] -> die "identifier without type or stray type name"
  in
  loop strings

let prog_of_sexps (sexps: CCSexp.t list) =
  let rec expr_of_sexp sexp =
    match sexp with
    | `Atom v ->
      let c = v.[0] in
      if Char.code c >= Char.code '0' && Char.code c <= Char.code '9' then (
        let x = int_of_string v in
        if x > 0xFF then
          die "%d: integer litteral larger than 8 bits (use #... to specify a 16 bits literal)" x;
        Econst (C8 x)
      ) else if Char.equal c '#' then (
        let x = int_of_string (strtl v) in
        if x > 0xFFFF then
          die "%d: integer litteral larger than 16 bits" x;
        Econst (C16 x)
      ) else if Char.equal c '\'' then
        Econst (C8 (Char.code v.[1]))
      else
        Evar v
    | `List [`Atom "&"; `Atom v] -> Eaddr v
    | `List [e1; `Atom "+"; e2] -> Ebinop (Oadd, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "-"; e2] -> Ebinop (Osub, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "/"; e2] -> Ebinop (Odiv, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "*"; e2] -> Ebinop (Omul, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "and"; e2] -> Ebinop (Oand, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "or"; e2] -> Ebinop (Oor, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "xor"; e2] -> Ebinop (Oor, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "<"; e2] -> Ebinop (Ocmp Lt, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom ">"; e2] -> Ebinop (Ocmp Gt, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "="; e2] -> Ebinop (Ocmp Eq, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "!="; e2] -> Ebinop (Ocmp Neq, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e; `Atom "as"; `Atom ty] -> Ecast (expr_of_sexp e, ty_of_string ty)
    | `List [`Atom "*"; e] -> Eload (expr_of_sexp e)
    | _ -> die "Ill formed expression: %s" (CCSexp.to_string sexp)
  in

  let builtin_of_string = function
    | "putchar" -> EF_putchar
    | "malloc" -> EF_malloc
    | s -> die "unknown builtin %s" s
  in

  let rec stmt_of_sexps sexps =
    match sexps with
    | [] -> Sskip
    | se :: sse ->
      let s =
        match se with
        (* Sassign: (v = e) *)
        | `List [`Atom v; `Atom "="; e] -> Sassign (v, expr_of_sexp e)
        (* Sstore: (e1 := e2) *)
        | `List [e1; `Atom ":="; e2] -> Sstore (expr_of_sexp e1, expr_of_sexp e2)

        (* Sifthenelse: (ifte cond (...) (...)) *)
        | `List [`Atom "ifte"; cond; `List iftrue; `List iffalse] ->
          Sifthenelse (expr_of_sexp cond, stmt_of_sexps iftrue, stmt_of_sexps iffalse)

        (* Sloop: (while cond (...)) *)
        | `List [`Atom "while"; cond; `List body] ->
          Sloop (expr_of_sexp cond, stmt_of_sexps body)

        (* Sbuiltin:
           (v <- ! ef args...)
           (! ef args...)
        *)
        | `List (`Atom v :: `Atom "<-" :: `Atom "!" :: `Atom b :: args) ->
          Sbuiltin (Some v, builtin_of_string b, List.map expr_of_sexp args)
        | `List (`Atom "!" :: `Atom b :: args) ->
          Sbuiltin (None, builtin_of_string b, List.map expr_of_sexp args)

        (* Scall:
           (v <- f args...)
           (f args...)
        *)
        | `List (`Atom v :: `Atom "<-" :: `Atom f :: args) ->
          Scall (Some v, f, List.map expr_of_sexp args)
        | `List (`Atom f :: args) ->
          Scall (None, f, List.map expr_of_sexp args)

        | _ -> die "Ill formed statement: %s" (CCSexp.to_string se)
      in
      Sseq (s, stmt_of_sexps sse)
  in

  (*
     (:ty f (:ty x :ty y :ty z)       ; parameters
        (local :ty u :ty v :ty w) ; local variables
        ( ... )       ; body
        (ret e)       ; return clause
     )
  *)
  let func_of_sexp sexp =
    match sexp with
    | `List (
        `Atom ret_ty ::
        `Atom f ::
        `List params ::
        `List (`Atom "local" :: locals) ::
        rest
      )
      ->
      let body, last = CCList.take_drop (List.length rest - 1) rest in
      let ret =
        match last with
        | [`List [`Atom "ret"; e]] -> Some (expr_of_sexp e)
        | [`List [`Atom "ret"]] -> None
        | _ -> die "missing return clause"
      in
      let ret_ty = ty_of_string ret_ty in
      let params = typed_idents_of_sexps params in
      let locals = typed_idents_of_sexps locals in
      let body = stmt_of_sexps body in
      f,
      { fn_params = params;
        fn_vars = locals;
        fn_body = body;
        fn_ret = ret;
        fn_ret_ty = ret_ty }
    | _ -> die "Ill-formed function declaration"
  in

  let prog_main, prog_defs =
    match sexps with
    | [] -> die "Empty file"
    | `List [`Atom main] :: defs -> main, defs
    | _ -> die "Incorrect or absent main header"
  in

  { prog_defs = List.map func_of_sexp prog_defs;
    prog_main }

