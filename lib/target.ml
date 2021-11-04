type opcode =
  | LDZ
  | LDA
  | STA
  | STZ
  | ADD
  | SUB
  | DIV
  | MUL
  | SWP
  | LTH
  | GTH
  | AND
  | ORA
  | EOR
  | SFT
  | EQU
  | NEQ
  | JSR
  | JCN
  | JMP
  | POP
  | BRK
  | ROT
  | NIP
  | DUP
  | STH
  | DEO
  | DEI

type opcode_flags =
  { keep : bool;
    return : bool;
    short : bool }

type opflag = K | R | S
let opflags_to_flags l =
  List.fold_left (fun (fs: opcode_flags) f ->
    match f with
    | K -> { fs with keep = true }
    | R -> { fs with return = true }
    | S -> { fs with short = true }
  ) { keep = false; return = false; short = false } l

type inst =
  | I of opcode * opcode_flags
  | Idat of int (* byte *)
  | Idat16 of int (* short *)
  | IdatR of int (* byte *)
  | Idat16R of int (* short *)
  | Iraw of int (* byte *)
  | Iraw16 of int (* short *)
  (* comment (has no semantics) *)
  | Icomment of string

let i (opcode: opcode) (flags: opflag list) =
  I (opcode, opflags_to_flags flags)

let inst_size = function
  | I _ -> 1
  | Idat _ | IdatR _ -> 2 (* LIT + 1 byte *)
  | Idat16 _ | Idat16R _ -> 3 (* LIT + 2 bytes *)
  | Iraw _ -> 1
  | Iraw16 _ -> 2
  | Icomment _ -> 0

(* type inst =
 *   (\* arithmetic *\)
 *   | IConst of reg * int64
 *   | IMov of reg * reg
 *   | IAdd of reg * reg
 *   | ISub of reg * reg
 *   | IDiv of reg
 *   | ILt of reg * reg
 *   | IEqual of reg * reg
 *   (\* jumps *\)
 *   | IJump of cond * int
 *   | ICall of int
 *   (\* stack *\)
 *   | IRet
 *   | IPop of reg
 *   | IPush of reg
 *   | IAdd_RSP of int
 *   | ISub_RSP of int
 *   | ILoad_RSP of reg * int
 *   | IStore_RSP of reg * int
 *   | IGet_RSP of reg * int
 *   (\* memory *\)
 *   | ILoad of reg * reg * int
 *   | IStore of reg * reg * int
 *   (\* I/O *\)
 *   | IPutChar
 *   | IExit
 *   (\* comment (has no semantics) *\)
 *   | IComment of string *)

type asm = inst list

let pp_lab ppf n = Format.fprintf ppf "L%d" n

let pp_opcode ppf = function
  | LDZ -> Format.fprintf ppf "LDZ"
  | LDA -> Format.fprintf ppf "LDA"
  | STA -> Format.fprintf ppf "STA"
  | STZ -> Format.fprintf ppf "STZ"
  | ADD -> Format.fprintf ppf "ADD"
  | SUB -> Format.fprintf ppf "SUB"
  | DIV -> Format.fprintf ppf "DIV"
  | MUL -> Format.fprintf ppf "MUL"
  | AND -> Format.fprintf ppf "AND"
  | ORA -> Format.fprintf ppf "ORA"
  | EOR -> Format.fprintf ppf "EOR"
  | SWP -> Format.fprintf ppf "SWP"
  | LTH -> Format.fprintf ppf "LTH"
  | GTH -> Format.fprintf ppf "GTH"
  | SFT -> Format.fprintf ppf "SFT"
  | EQU -> Format.fprintf ppf "EQU"
  | NEQ -> Format.fprintf ppf "NEQ"
  | JSR -> Format.fprintf ppf "JSR"
  | JCN -> Format.fprintf ppf "JCN"
  | JMP -> Format.fprintf ppf "JMP"
  | POP -> Format.fprintf ppf "POP"
  | BRK -> Format.fprintf ppf "BRK"
  | ROT -> Format.fprintf ppf "ROT"
  | NIP -> Format.fprintf ppf "NIP"
  | DUP -> Format.fprintf ppf "DUP"
  | STH -> Format.fprintf ppf "STH"
  | DEO -> Format.fprintf ppf "DEO"
  | DEI -> Format.fprintf ppf "DEI"

let pp_opcode_flags ppf (f: opcode_flags) =
  Format.fprintf ppf "%s%s%s"
    (if f.keep then "k" else "")
    (if f.return then "r" else "")
    (if f.short then "2" else "")

let pp_inst ppf = function
  | I (op, flags) -> Format.fprintf ppf "%a%a" pp_opcode op pp_opcode_flags flags
  | Idat x -> Format.fprintf ppf "#%.2x" (x land 0xFF)
  | Idat16 x -> Format.fprintf ppf "#%.4x" (x land 0xFFFF)
  | IdatR x -> Format.fprintf ppf "LITr %.2x" (x land 0xFF)
  | Idat16R x -> Format.fprintf ppf "LIT2r %.4x" (x land 0xFFFF)
  | Iraw x -> Format.fprintf ppf "%.2x" (x land 0xFF)
  | Iraw16 x -> Format.fprintf ppf "%.4x" (x land 0xFFFF)
  | Icomment s -> Format.fprintf ppf "( %s )" s

let pp_insts off ppf insts =
  List.fold_left (fun off inst ->
    Format.fprintf ppf "(%x) %a\n" off pp_inst inst;
    off + inst_size inst
  ) off insts |> ignore

let pp_asm off ppf asm =
  Format.fprintf ppf "|0100\n";
  Format.fprintf ppf "%a"
    (pp_insts off) asm

let assemble_opcode = function
  | BRK -> 0x00
  | POP -> 0x02
  | DUP -> 0x03
  | NIP -> 0x04
  | SWP -> 0x05
  | ROT -> 0x07
  | EQU -> 0x08
  | NEQ -> 0x09
  | GTH -> 0x0a
  | LTH -> 0x0b
  | JMP -> 0x0c
  | JCN -> 0x0d
  | JSR -> 0x0e
  | STH -> 0x0f
  | LDZ -> 0x10
  | STZ -> 0x11
  | LDA -> 0x14
  | STA -> 0x15
  | DEI -> 0x16
  | DEO -> 0x17
  | ADD -> 0x18
  | SUB -> 0x19
  | MUL -> 0x1a
  | DIV -> 0x1b
  | AND -> 0x1c
  | ORA -> 0x1d
  | EOR -> 0x1e
  | SFT -> 0x1f

let assemble_opcode_with_flags opcode flags =
  assemble_opcode opcode
  lor (if flags.short then 0x20 else 0)
  lor (if flags.return then 0x40 else 0)
  lor (if flags.keep then 0x80 else 0)

let assemble_inst = function
  | I (opcode, flags) -> [assemble_opcode_with_flags opcode flags]
  | Idat n -> [0x80 (* LIT *); n land 0xff]
  | Idat16 n -> [0x20 (* LIT2 *); (n lsr 8) land 0xff; n land 0xff]
  | IdatR n -> [0xc0 (* LITr *); n land 0xff]
  | Idat16R n -> [0xe0 (* LIT2r *); (n lsr 8) land 0xff; n land 0xff]
  | Iraw n -> [n land 0xff]
  | Iraw16 n -> [(n lsr 8) land 0xff; n land 0xff]
  | Icomment _ -> []

let assemble prog =
  List.concat_map assemble_inst prog
