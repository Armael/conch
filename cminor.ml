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

type expr =
  | Evar of ident
  | Eaddr of ident
  | Econst of int
  | Ebinop of binary_op * expr * expr
  | Eload of expr

type external_function =
  | EF_putchar
  | EF_malloc

type stmt =
  | Sskip
  | Sassign of ident * expr
  | Sstore of expr * expr
  | Scall of ident option * ident * expr list
  | Sbuiltin of ident option * external_function * expr list
  | Sseq of stmt * stmt
  | Sifthenelse of expr * stmt * stmt
  | Sloop of expr * stmt

type func = {
  fn_params : ident list;
  fn_vars : ident list;
  fn_body : stmt;
  fn_ret : expr option;
}

type program = {
  prog_defs : (ident * func) list;
  prog_main : ident;
}
