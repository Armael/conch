open Common
open Types

type uexpr =
  | Evar of ident
  | Eaddr of ident
  | Econst of const
  | Ebinop of binary_op * expr * expr
  | Eload of expr
  | Ecast of expr * ty
  | Ecall of ident * expr list
  | Ebuiltin of external_function * expr list
and expr = uexpr * ty

type stmt =
  | Sskip
  | Sdo of expr
  | Sassign of ident * expr
  | Sstore of expr * expr
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

type glob = {
  gl_ty : ty;
  gl_init : const option;
}

type genv = {
  genv_globs : ty IdentMap.t;
  genv_funs : (ty * ty list) IdentMap.t;
}

type program = {
  prog_genv : genv;
  prog_fundecls : (ident * func) list;
  prog_globdecls : (ident * glob) list;
  prog_main : ident;
}

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

let string_of_builtin = function
  | EF_putchar -> "putchar"
  | EF_malloc -> "malloc"
  | EF_out -> "out"
  | EF_in8 -> "in8"
  | EF_in16 -> "in16"

let rec pp_expr fmt e =
  match fst e with
  | Evar v -> Format.fprintf fmt "%s" v
  | Eaddr v -> Format.fprintf fmt "(& %s)" v
  | Econst (C8 x) -> Format.fprintf fmt "%d" x
  | Econst (C16 x) -> Format.fprintf fmt "#%d" x
  | Ebinop (op, e1, e2) ->
    Format.fprintf fmt "(%a %s %a)" pp_expr e1 (string_of_op op) pp_expr e2
  | Eload e -> Format.fprintf fmt "(* %a)" pp_expr e
  | Ecast (e, ty) -> Format.fprintf fmt "(%a as %a)" pp_expr e pp_ty ty
  | Ecall (f, es) ->
    Format.fprintf fmt "(%s" f;
    List.iter (fun e -> Format.fprintf fmt " %a" pp_expr e) es;
    Format.fprintf fmt ")"
  | Ebuiltin (ef, es) ->
    Format.fprintf fmt "(! %s" (string_of_builtin ef);
    List.iter (fun e -> Format.fprintf fmt " %a" pp_expr e) es;
    Format.fprintf fmt ")"
