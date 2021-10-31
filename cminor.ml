open Common
open Types

type uexpr =
  | Evar of ident
  | Eglob of int (* offset in the globals table *)
  | Eaddr of ident
  | Econst of const
  | Ebinop of binary_op * expr * expr
  | Eload of expr
  | Ecast of expr * ty
and expr = uexpr * ty

type stmt =
  | Sskip
  | Sassign of ident * expr
  | Sassign_glob of int (* offset *) * expr
  | Sstore of expr * expr
  | Scall of ident option * ident * expr list
  | Sbuiltin of ident option * external_function * expr list
  | Sseq of stmt * stmt
  | Sifthenelse of expr * stmt * stmt
  | Sloop of expr * stmt

type lenv = ty IdentMap.t

type func = {
  fn_lenv : lenv;
  fn_params : (ident * ty) list;
  fn_vars : (ident * ty) list;
  fn_body : stmt;
  fn_ret : expr option;
  fn_ret_ty : ty;
}

type genv = (ty * ty list) IdentMap.t

type program = {
  prog_genv : genv;
  prog_globs_tbl_size : int; (* in bytes *)
  prog_defs : (ident * func) list;
  prog_main : ident;
}

(* conversion to sexps *)

let string_of_glob n =
  "@" ^ string_of_int n

let rec sexp_of_expr (e: expr) =
  match fst e with
  | Evar v -> `Atom v
  | Eglob n -> `Atom (string_of_glob n)
  | Eaddr v -> `List [`Atom "&"; `Atom v]
  | Econst c -> `Atom (string_of_const c)
  | Ebinop (op, e1, e2) ->
    `List [sexp_of_expr e1;
           `Atom (string_of_op op);
           sexp_of_expr e2]
  | Eload e -> `List [`Atom "*"; sexp_of_expr e]
  | Ecast (e, ty) ->
    `List [sexp_of_expr e; `Atom (string_of_ty ty)]

let rec sexps_of_stmt (s: stmt) =
  match s with
  | Sskip -> []
  | Sassign (v, e) ->
    [`List [`Atom v; `Atom "="; sexp_of_expr e]]
  | Sassign_glob (v, e) ->
    [`List [`Atom (string_of_glob v); sexp_of_expr e]]
  | Sstore (e1, e2) ->
    [`List [sexp_of_expr e1; `Atom ":="; sexp_of_expr e2]]
  | Scall (ret, f, es) ->
    begin match ret with
    | None -> [`List (`Atom f :: List.map sexp_of_expr es)]
    | Some ret ->
      [`List (`Atom ret :: `Atom "<-" :: `Atom f ::
              List.map sexp_of_expr es)]
    end
  | Sbuiltin (ret, ef, es) ->
    let f = string_of_builtin ef in
    begin match ret with
    | None -> [`List (`Atom f :: List.map sexp_of_expr es)]
    | Some ret ->
      [`List (`Atom ret :: `Atom "<-" :: `Atom f ::
              List.map sexp_of_expr es)]
    end
  | Sseq (s1, s2) ->
    sexps_of_stmt s1 @ sexps_of_stmt s2
  | Sifthenelse (e, s1, s2) ->
    [`List [`Atom "ifte"; sexp_of_expr e;
            `List (sexps_of_stmt s1); `List (sexps_of_stmt s2)]]
  | Sloop (e, s) ->
    [`List [`Atom "loop"; sexp_of_expr e; `List (sexps_of_stmt s)]]

let sexps_of_typed_idents (l: (ident * ty) list) =
  List.concat_map (fun (id, ty) ->
    [`Atom (string_of_ty ty); `Atom id]
  ) l

let sexp_of_func fname (f: func) =
  `List (
    `Atom (string_of_ty f.fn_ret_ty) ::
    `Atom fname ::
    `List (sexps_of_typed_idents f.fn_params) ::
    `List (`Atom "local" :: sexps_of_typed_idents f.fn_vars) ::
    sexps_of_stmt f.fn_body @
    (match f.fn_ret with
     | None -> [`List [`Atom "ret"]]
     | Some ret -> [`List [`Atom "ret"; sexp_of_expr ret]])
  )

let sexps_of_prog (p: program) =
  List.map (fun (fname, f) -> sexp_of_func fname f) p.prog_defs

(* helpers *)

let type_of_expr (e: expr): ty =
  snd e

(* smart constructors *)

let sseq s1 s2 =
  match s1, s2 with
  | Sskip, Sskip -> Sskip
  | Sskip, s | s, Sskip -> s
  | _, _ -> Sseq (s1, s2)
