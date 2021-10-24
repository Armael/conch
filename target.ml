type opcode =
  | LIT
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
  | DEO

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
  (* comment (has no semantics) *)
  | Icomment of string

let i (opcode: opcode) (flags: opflag list) =
  I (opcode, opflags_to_flags flags)

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
  | LIT -> Format.fprintf ppf "LIT"
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
  | DEO -> Format.fprintf ppf "DEO"

let pp_opcode_flags ppf (f: opcode_flags) =
  Format.fprintf ppf "%s%s%s"
    (if f.keep then "k" else "")
    (if f.return then "r" else "")
    (if f.short then "2" else "")

let pp_inst ppf = function
  (* | IConst (r, imm) -> Format.fprintf ppf "movq $%Ld, %a" imm pp_reg r
   * | IMov (dst, src) -> Format.fprintf ppf "movq %a, %a" pp_reg src pp_reg dst
   * | IAdd (dst, src) -> Format.fprintf ppf "addq %a, %a" pp_reg src pp_reg dst
   * | ISub (dst, src) -> Format.fprintf ppf "subq %a, %a" pp_reg src pp_reg dst
   * | ILt (r1, r2) -> Format.fprintf ppf "cmpq %a, %a ; setl %%al ; movzbl %%al, %%eax" pp_reg r2 pp_reg r1
   * | IEqual (r1, r2) ->
   *   Format.fprintf ppf "cmpq %a, %a ; sete %%al ; movzbl %%al, %%eax" pp_reg r1 pp_reg r2
   * | IDiv r -> Format.fprintf ppf "divq %a" pp_reg r
   * | IJump (CAlways, n) -> Format.fprintf ppf "jmp %a" pp_lab n
   * | IJump (CIfTrue r, n) -> Format.fprintf ppf "cmpq $0, %a ; jne %a" pp_reg r pp_lab n
   * | IJump (CIfFalse r, n) -> Format.fprintf ppf "cmpq $0, %a ; je %a" pp_reg r pp_lab n
   * | ICall n -> Format.fprintf ppf "call %a" pp_lab n
   * | IRet -> Format.fprintf ppf "ret"
   * | IPop r -> Format.fprintf ppf "popq %a" pp_reg r
   * | IPush r -> Format.fprintf ppf "pushq %a" pp_reg r
   * | ILoad_RSP (r, n) -> Format.fprintf ppf "movq %d(%%rsp), %a" (8*n) pp_reg r
   * | IStore_RSP (r, n) -> Format.fprintf ppf "movq %a, %d(%%rsp)" pp_reg r (8*n)
   * | IGet_RSP (r, n) -> Format.fprintf ppf "movq %%rsp, %a ; addq $%d, %a" pp_reg r (8*n) pp_reg r (\* TODO: check *\)
   * | IAdd_RSP n -> Format.fprintf ppf "addq $%d, %%rsp" (8*n)
   * | ISub_RSP n -> Format.fprintf ppf "subq $%d, %%rsp" (8*n)
   * | IStore (src, a, w) -> Format.fprintf ppf "movq %a, %d(%a)" pp_reg src w pp_reg a
   * | ILoad (dst, a, w) -> Format.fprintf ppf "movq %d(%a), %a" w pp_reg a pp_reg dst
   * | IPutChar -> Format.fprintf ppf "movq stdout(%%rip), %%rsi ; call _IO_putc@PLT"
   * | IExit -> Format.fprintf ppf "call exit@PLT" *)
  | I (op, flags) -> Format.fprintf ppf "%a%a" pp_opcode op pp_opcode_flags flags
  | Idat x -> Format.fprintf ppf "#%.2x" (x land 0xFF)
  | Idat16 x -> Format.fprintf ppf "#%.4x" (x land 0xFFFF)
  | Icomment _s -> (*Format.fprintf ppf "/* %s */" s*) ()

let pp_insts _off ppf insts =
  List.iteri (fun _i inst ->
    Format.fprintf ppf "%a\n" pp_inst inst
  ) insts

let pp_asm ppf asm =
(*   Format.fprintf ppf "
 * \t.bss
 * \t.p2align 3 /* 8-byte align */
 * heapS:
 * \t.space 8*1024*1024 /* bytes of heap space */
 * \t.p2align 3 /* 8-byte align */
 * heapE:
 * \t.text
 * \t.globl main
 * main:
 * \tsubq $8, %%rsp /* 16-byte align %%rsp */
 * \tmovabs $heapS, %%r14 /* r14 := heap start */
 * \tmovabs $heapE, %%r15 /* r15 := heap end */
 * %a
 * " *)
  Format.fprintf ppf "%a"
    (pp_insts 0) asm

let assemble_opcode = function
  | BRK -> 0x00
  | LIT -> 0x00 (* XXX: LIT with no flags is BRK *)
  | POP -> 0x02
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
  | LDZ -> 0x10
  | STZ -> 0x11
  | LDA -> 0x14
  | STA -> 0x15
  (* | DEI -> 0x16 *)
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
  let flags =
    if opcode = LIT then { flags with keep = true } else flags
  in
  assemble_opcode opcode
  lor (if flags.short then 0x20 else 0)
  lor (if flags.return then 0x40 else 0)
  lor (if flags.keep then 0x80 else 0)

let assemble_inst = function
  | I (opcode, flags) -> [assemble_opcode_with_flags opcode flags]
  | Idat n -> [n land 0xff]
  | Idat16 n -> [n lsr 8; n land 0xff] (* XXX todo check *)
  | Icomment _ -> []

let assemble prog =
  List.concat_map assemble_inst prog
