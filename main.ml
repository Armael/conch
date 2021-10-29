open Cminor
open Containers

let die fmt =
  Printf.kprintf (fun s -> Printf.eprintf "ERR: %s\n" s; exit 1) fmt

let strings_of_sexps s =
  List.map (function `Atom s -> s | `List _ -> die "expected a string") s

let prog_of_sexps (sexps: CCSexp.t list) =
  let rec expr_of_sexp sexp =
    match sexp with
    | `Atom v ->
      let c = v.[0] in
      if Char.code c >= Char.code '0' && Char.code c <= Char.code '9' then
        Econst (int_of_string v)
      else if Char.equal c '$' then
        Econst (Char.code v.[1])
      else
        Evar v
    | `List [`Atom "&"; `Atom v] -> Eaddr v
    | `List [`Atom "#"; `Atom c] -> Econst (int_of_string c)
    | `List [`Atom "c"; `Atom c] -> Econst (Char.code c.[0])
    | `List [e1; `Atom "+"; e2] -> Ebinop (Oadd, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "-"; e2] -> Ebinop (Osub, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "/"; e2] -> Ebinop (Odiv, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "*"; e2] -> Ebinop (Omul, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "and"; e2] -> Ebinop (Oand, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "or"; e2] -> Ebinop (Oor, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "xor"; e2] -> Ebinop (Oor, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "<"; e2] -> Ebinop (Ocmp Lt, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom ">"; e2] -> Ebinop (Ocmp Gt, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "="; e2] -> Ebinop (Ocmp Eq, expr_of_sexp e1, expr_of_sexp e2)
    | `List [e1; `Atom "!="; e2] -> Ebinop (Ocmp Neq, expr_of_sexp e1, expr_of_sexp e2)
    | `List [`Atom "*"; e] -> Eload (expr_of_sexp e)
    | _ -> die "Ill formed expression: %s" (CCSexp.to_string sexp)
  in

  let builtin_of_string = function
    | "putchar" -> EF_putchar
    | "malloc" -> EF_malloc
    | s -> die "unknown builtin %s" s
  in

  let rec stmt_of_sexps sexps =
    match sexps with
    | [] -> Sskip
    | se :: sse ->
      let s =
        match se with
        (* Sassign: (v = e) *)
        | `List [`Atom v; `Atom "="; e] -> Sassign (v, expr_of_sexp e)
        (* Sstore: (e1 := e2) *)
        | `List [e1; `Atom ":="; e2] -> Sstore (expr_of_sexp e1, expr_of_sexp e2)

        (* Sifthenelse: (ifte cond (...) (...)) *)
        | `List [`Atom "ifte"; cond; `List iftrue; `List iffalse] ->
          Sifthenelse (expr_of_sexp cond, stmt_of_sexps iftrue, stmt_of_sexps iffalse)

        (* Sloop: (while cond (...)) *)
        | `List [`Atom "while"; cond; `List body] ->
          Sloop (expr_of_sexp cond, stmt_of_sexps body)

        (* Sbuiltin:
           (v <- ! ef args...)
           (! ef args...)
        *)
        | `List (`Atom v :: `Atom "<-" :: `Atom "!" :: `Atom b :: args) ->
          Sbuiltin (Some v, builtin_of_string b, List.map expr_of_sexp args)
        | `List (`Atom "!" :: `Atom b :: args) ->
          Sbuiltin (None, builtin_of_string b, List.map expr_of_sexp args)

        (* Scall:
           (v <- f args...)
           (f args...)
        *)
        | `List (`Atom v :: `Atom "<-" :: `Atom f :: args) ->
          Scall (Some v, f, List.map expr_of_sexp args)
        | `List (`Atom f :: args) ->
          Scall (None, f, List.map expr_of_sexp args)

        | _ -> die "Ill formed statement: %s" (CCSexp.to_string se)
      in
      Sseq (s, stmt_of_sexps sse)
  in

  (*
     (f (x y z)       ; parameters
        (local u v w) ; local variables
        ( ... )       ; body
        (ret e)       ; return clause
     )
  *)
  let func_of_sexp sexp =
    match sexp with
    | `List (
        `Atom f ::
        `List params ::
        `List (`Atom "local" :: locals) ::
        rest
      )
      ->
      let body, last = CCList.take_drop (List.length rest - 1) rest in
      let ret =
        match last with
        | [`List [`Atom "ret"; e]] -> Some (expr_of_sexp e)
        | [`List [`Atom "ret"]] -> None
        | _ -> die "missing return clause"
      in
      let params = strings_of_sexps params in
      let locals = strings_of_sexps locals in
      let body = stmt_of_sexps body in
      f,
      { fn_params = params;
        fn_vars = locals;
        fn_body = body;
        fn_ret = ret }
    | _ -> die "Ill formed function declaration"
  in

  let prog_main, prog_defs =
    match sexps with
    | [] -> die "Empty file"
    | `List [`Atom main] :: defs -> main, defs
    | _ -> die "Incorrect or absent main header"
  in

  { prog_defs = List.map func_of_sexp prog_defs;
    prog_main }

let () =
  let input, output =
    match Sys.argv |> Array.to_list |> List.tl with
    | [input_file; output_file] -> input_file, output_file
    | _ -> Printf.eprintf "Usage: %s <input file> <output.rom>\n" Sys.argv.(0); exit 1
  in
  match CCSexp.parse_file_list input with
  | Error err -> die "Cannot parse input file: %s" err
  | Ok sexps ->
    let prog = prog_of_sexps sexps in
    let asm = Codegen.program prog in
    Format.fprintf Format.std_formatter "%a\n" (Target.pp_asm Codegen.prog_start) asm;
    let bytes = Target.assemble asm in
    let out = open_out output in
    List.iter (output_byte out) bytes;
    close_out out
