type tybase = Tvoid | Tint8 | Tint16
type ty =
  | Tbase of tybase
  | Tptr of ty

(* in bytes *)
let sizeof = function
  | Tbase Tvoid -> 0
  | Tbase Tint8 -> 1
  | Tbase Tint16 | Tptr _ -> 2

