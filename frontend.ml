open Common
open Types
open Lang

(* sexps -> typed lang AST, using the "smart constructors" from Typing *)

let die fmt = Common.die ~where:"frontend" fmt

let strtl s = String.sub s 1 (String.length s - 1)
let char_at s i c =
  try Char.equal (String.get s i) c
  with Invalid_argument _ -> false

let ty_of_string str =
  let rec aux s =
    if char_at s 0 '*' then Tptr (aux (strtl s))
    else if String.equal s "void" then Tbase Tvoid
    else if String.equal s "u8" then Tbase Tint8
    else if String.equal s "u16" then Tbase Tint16
    else die "cannot parse type %s" str
  in
  if char_at str 0 ':' then aux (strtl str)
  else die "cannot parse type %s" str

let typed_idents_of_sexps s : (ident * ty) list =
  let strings =
    List.map (function `Atom s -> s | `List _ -> die "expected an identifier or a type name") s in
  let rec loop = function
  | ty :: ident :: rest -> (ident, ty_of_string ty) :: loop rest
  | [] -> []
  | [_] -> die "identifier without type or stray type name"
  in
  loop strings

let builtin_of_string = function
  | "putchar" -> EF_putchar
  | "malloc" -> EF_malloc
  | "out" -> EF_out
  | "in8" -> EF_in8
  | "in16" -> EF_in16
  | s -> die "unknown builtin %s" s

let const_of_string v =
  let c = v.[0] in
  if Char.code c >= Char.code '0' && Char.code c <= Char.code '9' then (
    let x = int_of_string v in
    if x > 0xFF then
      die "%d: integer litteral larger than 8 bits (use #... to specify a 16 bits literal)" x;
    Some (C8 x)
  ) else if Char.equal c '#' then (
    let x = int_of_string (strtl v) in
    if x > 0xFFFF then
      die "%d: integer litteral larger than 16 bits" x;
    Some (C16 x)
  ) else if Char.equal c '\'' then
    Some (C8 (Char.code v.[1])
  ) else
    None

let rec expr_of_sexp genv lenv sexp : expr =
  let expr_of_sexp = expr_of_sexp genv lenv in
  match sexp with
  | `Atom v ->
    begin match const_of_string v with
    | Some c -> Typing.econst c
    | None -> Typing.evar genv lenv v
    end
  | `List [`Atom "&"; `Atom v] -> Typing.eaddr genv lenv v
  | `List [e1; `Atom "+"; e2] -> Typing.ebinop Oadd (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e1; `Atom "-"; e2] -> Typing.ebinop Osub (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e1; `Atom "/"; e2] -> Typing.ebinop Odiv (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e1; `Atom "*"; e2] -> Typing.ebinop Omul (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e1; `Atom "and"; e2] -> Typing.ebinop Oand (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e1; `Atom "or"; e2] -> Typing.ebinop Oor (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e1; `Atom "xor"; e2] -> Typing.ebinop Oor (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e1; `Atom "<"; e2] -> Typing.ebinop (Ocmp Lt) (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e1; `Atom ">"; e2] -> Typing.ebinop (Ocmp Gt) (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e1; `Atom "="; e2] -> Typing.ebinop (Ocmp Eq) (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e1; `Atom "!="; e2] -> Typing.ebinop (Ocmp Neq) (expr_of_sexp e1) (expr_of_sexp e2)
  | `List [e; `Atom "as"; `Atom ty] -> Typing.ecast (expr_of_sexp e) (ty_of_string ty)
  | `List [`Atom "*"; e] -> Typing.eload (expr_of_sexp e)
  | `List ((`Atom f) :: es) ->
    let es = List.map expr_of_sexp es in
    if char_at f 0 '!' then (
      (* builtin *)
      let builtin = builtin_of_string (strtl f) in
      Typing.ebuiltin builtin es
    ) else
      Typing.ecall genv f es
  | _ -> die "Ill-formed expression: %s" (CCSexp.to_string sexp)

let rec stmt_of_sexps genv lenv sexps : stmt =
  let stmt_of_sexps = stmt_of_sexps genv lenv in
  let expr_of_sexp = expr_of_sexp genv lenv in
  match sexps with
  | [] -> Typing.sskip
  | se :: sse ->
    let s =
      match se with
      (* Sassign: (v = e) *)
      | `List [`Atom v; `Atom "="; e] -> Typing.sassign genv lenv v (expr_of_sexp e)
      (* Sstore: (e1 := e2) *)
      | `List [e1; `Atom ":="; e2] -> Typing.sstore (expr_of_sexp e1) (expr_of_sexp e2)

      (* Sifthenelse: (ifte cond (...) (...)) *)
      | `List [`Atom "ifte"; cond; `List iftrue; `List iffalse] ->
        Typing.sifthenelse (expr_of_sexp cond) (stmt_of_sexps iftrue) (stmt_of_sexps iffalse)

      (* Sloop: (while cond (...)) *)
      | `List [`Atom "while"; cond; `List body] ->
        Typing.sloop (expr_of_sexp cond) (stmt_of_sexps body)

      (* Sdo: e *)
      | _ -> Typing.sdo (expr_of_sexp se)
    in
    Sseq (s, stmt_of_sexps sse)

(*
   global declaration:

   (:ty g)      ; without initial value
   (:ty g = 42) ; with initial value

   function declaration:

   (:ty f (:ty x :ty y :ty z)   ; parameters
      (local :ty u :ty v :ty w) ; local variables
      ( ... )       ; body
      (ret e)       ; return clause
   )
*)
let classify_decl sexp =
  match sexp with
  | `List [`Atom ty; `Atom name] ->
    `Glob (ty_of_string ty, name, None)
  | `List [`Atom ty; `Atom name; `Atom "="; `Atom c] ->
    begin match const_of_string c with
    | Some c -> `Glob (ty_of_string ty, name, Some c)
    | None -> die "illegal global initializer: %s" c
    end
  | `List (
    `Atom ret_ty ::
    `Atom f ::
    `List params ::
    `List (`Atom "local" :: locals) ::
    rest
  ) ->
    let body, last = CCList.take_drop (List.length rest - 1) rest in
    let ret =
      match last with
      | [`List [`Atom "ret"; e]] -> Some e
      | [`List [`Atom "ret"]] -> None
      | _ -> die "missing return clause"
    in
    let ret_ty = ty_of_string ret_ty in
    let params = typed_idents_of_sexps params in
    let locals = typed_idents_of_sexps locals in
    `Fun (ret_ty, f, params, locals, body, ret)
  | _ -> die "Ill-formed declaration: %s" (CCSexp.to_string sexp)

let prog_of_sexps (sexps: CCSexp.t list) =
  if sexps = [] then die "Empty file";
  let decls = List.map classify_decl sexps in
  let proto_decls = List.map (function
    | `Glob (ty, s, _) -> `Glob (ty, s)
    | `Fun (ret_ty, f, params, _, _, _) -> `Fun (ret_ty, f, params)
  ) decls in

  (* build the global env *)
  let genv = Typing.build_genv proto_decls in

  let prog_globdecls, prog_fundecls =
    List.partition_map (function
      | `Glob (_, gname, init) ->
        Left (gname, Typing.glob genv gname init)
      | `Fun (_, fname, params, locals, body, ret) ->
        (* build the function's local env *)
        let lenv = Typing.build_lenv fname params locals in
        let body = stmt_of_sexps genv lenv body in
        let ret = Option.map (expr_of_sexp genv lenv) ret in
        Right (fname, Typing.func genv lenv fname params locals body ret)
    ) decls
  in

  if not (List.mem_assoc "main" prog_fundecls) then
    die "No 'main' entry point";

  { prog_genv = genv;
    prog_globdecls; prog_fundecls;
    prog_main = "main" }
