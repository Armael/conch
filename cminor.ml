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

(* helpers *)

let type_of_expr (e: expr): ty =
  snd e

(* smart constructors *)

let sseq s1 s2 =
  match s1, s2 with
  | Sskip, Sskip -> Sskip
  | Sskip, s | s, Sskip -> s
  | _, _ -> Sseq (s1, s2)
