let die ~where fmt =
  Format.kasprintf (fun s ->
    Format.fprintf Format.err_formatter "ERR (%s): %s\n" where s;
    exit 1
  ) fmt

type ident = string
module IdentMap : Map.S with type key := ident = Map.Make(String)

type const =
  | C8 of int
  | C16 of int

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

type external_function =
  | EF_putchar
  | EF_malloc
  | EF_out
  | EF_in8
  | EF_in16
