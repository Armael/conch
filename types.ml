type tybase = Tvoid | Tint8 | Tint16
type ty =
  | Tbase of tybase
  | Tptr of ty

(* in bytes *)
let sizeof = function
  | Tbase Tvoid -> 0
  | Tbase Tint8 -> 1
  | Tbase Tint16 | Tptr _ -> 2

(* printing *)

let pp_tybase fmt = function
  | Tvoid -> Format.fprintf fmt "void"
  | Tint8 -> Format.fprintf fmt "u8"
  | Tint16 -> Format.fprintf fmt "u16"

let rec pp_ty fmt = function
  | Tbase ty -> pp_tybase fmt ty
  | Tptr ty -> Format.fprintf fmt "*%a" pp_ty ty

let pp_ty fmt ty = pp_ty fmt ty

let string_of_ty ty =
  Format.asprintf ":%a" pp_ty ty
