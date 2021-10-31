open Common
open Types
open Lang
open Cminor

let gen_glob_offs glob_decls : int IdentMap.t * int =
  List.fold_left (fun (glob_offs, n) (gname, g) ->
    (IdentMap.add gname n glob_offs, n + sizeof g.gl_ty)
  ) (IdentMap.empty, 0) glob_decls

let mk_init_globs glob_offs glob_decls : Cminor.stmt =
  List.fold_left (fun init (gname, glob) ->
    match glob.gl_init with
    | None -> init
    | Some c ->
      let off = IdentMap.find gname glob_offs in
      Sseq (init, Sassign_glob (off, (Econst c, glob.gl_ty)))
  ) Sskip glob_decls

let gen_fresh_ident glenv lenv ty : ident * lenv (* updated lenv *) =
  let in_scope =
    Seq.append
      (IdentMap.to_seq glenv |> Seq.map fst)
      (IdentMap.to_seq lenv |> Seq.map fst)
  in
  let ids =
    in_scope
    |> Seq.filter_map (fun id ->
      try Scanf.sscanf id "_x%d" (fun x -> Some x)
      with Scanf.Scan_failure _ -> None
    )
    |> List.of_seq |> List.sort (Fun.flip compare)
  in
  let fresh_id =
    match ids with
    | x :: _ -> "_x" ^ (string_of_int (x+1))
    | [] -> "_x0"
  in
  fresh_id, IdentMap.add fresh_id ty lenv

let gete = function
  | Some e -> e
  | None ->
    (* typing invariant: the non-result of void expressions is not used as
       part of a larger expression *)
    assert false

let rec translate_expr glob_offs genv lenv (e: Lang.expr):
  Cminor.stmt *
  Cminor.expr option *
  (ident * ty) list * (* new local variables *)
  lenv (* updated lenv *)
  =
  let ue, ty = e in
  let translate_exprs (es: Lang.expr list) :
    Cminor.stmt * Cminor.expr list * (ident * ty) list * lenv
    =
    let (s, ls, lenv), es' =
      List.fold_left_map (fun (sa, lsa, lenv) e ->
        let s, e', ls, lenv = translate_expr glob_offs genv lenv e in
        (Cminor.sseq sa s, lsa @ ls, lenv), gete e'
      ) (Sskip, [], lenv) es
    in
    s, es', ls, lenv
  in
  match ue with
  | Evar v ->
    if IdentMap.mem v lenv then
      Sskip, Some (Cminor.Evar v, ty), [], lenv
    else (* v is a global variable *)
      let goff = IdentMap.find v glob_offs in
      let gty = IdentMap.find v genv in
      Sskip, Some (Cminor.Eglob goff, gty), [], lenv
  | Eaddr v ->
    Sskip, Some (Cminor.Eaddr v, ty), [], lenv
  | Econst c ->
    Sskip, Some (Cminor.Econst c, ty), [], lenv
  | Ebinop (op, e1, e2) ->
    let s1, e1', ls1, lenv = translate_expr glob_offs genv lenv e1 in
    let s2, e2', ls2, lenv = translate_expr glob_offs genv lenv e2 in
    Cminor.sseq s1 s2,
    Some (Cminor.Ebinop (op, gete e1', gete e2'), ty),
    ls1 @ ls2,
    lenv
  | Eload e ->
    let s, e', ls, lenv = translate_expr glob_offs genv lenv e in
    s, Some (Cminor.Eload (gete e'), ty), ls, lenv
  | Ecast (e, to_ty) ->
    let s, e', ls, lenv = translate_expr glob_offs genv lenv e in
    s, Some (Cminor.Ecast (gete e', to_ty), ty), ls, lenv
  | Ecall (f, es) ->
    let s, es', ls, lenv = translate_exprs es in
    begin match ty with
    | Tbase Tvoid ->
      (* no expression to return *)
      Cminor.sseq s (Scall (None, f, es')),
      None, ls, lenv
    | _ ->
      let id, lenv = gen_fresh_ident genv lenv ty in
      Cminor.sseq s (Scall (Some id, f, es')),
      Some (Evar id, ty), ls, lenv
    end
  | Ebuiltin (ef, es) ->
    let s, es', ls, lenv = translate_exprs es in
    begin match ty with
    | Tbase Tvoid ->
      Cminor.sseq s (Sbuiltin (None, ef, es')),
      None, ls, lenv
    | _ ->
      let id, lenv = gen_fresh_ident genv lenv ty in
      Cminor.sseq s (Sbuiltin (Some id, ef, es')),
      Some (Evar id, ty), ls, lenv
    end

let rec translate_stmt glob_offs genv lenv (s: Lang.stmt):
  Cminor.stmt *
  (ident * ty) list * (* new local variables *)
  lenv (* updated lenv *)
  =
  match s with
  | Sskip -> Sskip, [], lenv
  | Sdo e ->
    let s', _e', ls, lenv = translate_expr glob_offs genv lenv e in
    (* e' is pure: it can be dropped safely *)
    s', ls, lenv
  | Sassign (v, e) ->
    let s', e', ls, lenv = translate_expr glob_offs genv lenv e in
    if IdentMap.mem v lenv then
      Cminor.sseq s' (Sassign (v, gete e')), ls, lenv
    else (* v is a global *)
      let gid = IdentMap.find v glob_offs in
      Cminor.sseq s' (Sassign_glob (gid, gete e')), ls, lenv
  | Sstore (e1, e2) ->
    let s1', e1', ls1, lenv = translate_expr glob_offs genv lenv e1 in
    let s2', e2', ls2, lenv = translate_expr glob_offs genv lenv e2 in
    Cminor.(sseq (sseq s1' s2') (Sstore (gete e1', gete e2'))),
    ls1 @ ls2, lenv
  | Sseq (s1, s2) ->
    let s1', ls1, lenv = translate_stmt glob_offs genv lenv s1 in
    let s2', ls2, lenv = translate_stmt glob_offs genv lenv s2 in
    Cminor.(sseq s1' s2'),
    ls1 @ ls2, lenv
  | Sifthenelse (e, s1, s2) ->
    let se, e', lse, lenv = translate_expr glob_offs genv lenv e in
    let s1', ls1, lenv = translate_stmt glob_offs genv lenv s1 in
    let s2', ls2, lenv = translate_stmt glob_offs genv lenv s2 in
    Cminor.(sseq se (Sifthenelse (gete e', s1', s2'))),
    lse @ ls1 @ ls2, lenv
  | Sloop (e, s) ->
    let se, e', lse, lenv = translate_expr glob_offs genv lenv e in
    let s', ls, lenv = translate_stmt glob_offs genv lenv s in
    Cminor.(sseq se (Sloop (gete e', s'))),
    lse @ ls, lenv

let translate_func glob_offs genv (f: Lang.func): Cminor.func =
  let body', ls, lenv = translate_stmt glob_offs genv f.fn_lenv f.fn_body in
  let ret_s, ret, ret_ls, lenv =
    match f.fn_ret with
    | None -> Sskip, None, [], lenv
    | Some ret ->
      let ret_s, ret', ls, lenv = translate_expr glob_offs genv lenv ret in
      ret_s, Some (gete ret'), ls, lenv
  in
  { fn_lenv = lenv; fn_params = f.fn_params;
    fn_vars = f.fn_vars @ ls @ ret_ls;
    fn_body = Cminor.sseq body' ret_s;
    fn_ret = ret;
    fn_ret_ty = f.fn_ret_ty }

let translate_prog (p: Lang.program): Cminor.program =
  let glob_offs, globs_tbl_size = gen_glob_offs p.prog_globdecls in
  let init_globs = mk_init_globs glob_offs p.prog_globdecls in
  let glenv = p.prog_genv.genv_globs in

  let prog_defs = List.map (fun (fname, f) ->
    (fname, translate_func glob_offs glenv f)
  ) p.prog_fundecls in

  (* add global initialization code to main *)
  let main_func = List.assoc p.prog_main prog_defs in
  let main_func = {
    main_func with
    fn_body = Cminor.sseq init_globs main_func.fn_body
  } in
  let prog_defs =
    List.map (fun (fname, f) ->
      if fname = p.prog_main then (fname, main_func)
      else (fname, f)
    ) prog_defs
  in

  { prog_genv = p.prog_genv.genv_funs;
    prog_globs_tbl_size = globs_tbl_size;
    prog_defs;
    prog_main = p.prog_main }
