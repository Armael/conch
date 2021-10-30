open Parsetree

let die fmt = Common.die ~where:"typing" fmt

(* in bytes *)
let sizeof = function
  | Tbase Tvoid -> 0
  | Tbase Tint8 -> 1
  | Tbase Tint16 | Tptr _ -> 2

type ty_expr =
  | Evar of ident
  | Eaddr of ident
  | Econst of const
  | Ebinop of binary_op * typed_expr * typed_expr
  | Eload of typed_expr
  | Ecast of typed_expr * ty
and typed_expr = ty_expr * ty

type typed_stmt = typed_expr stmt'

type typed_func = {
  tfn_params : ident list;
  tfn_params_ty : ty list;
  tfn_vars : ident list;
  tfn_idents_ty : ty IdentMap.t;
  tfn_body : typed_stmt;
  tfn_ret : typed_expr option;
  tfn_ret_ty : ty;
}

type typed_program = {
  typrog_defs : (ident * typed_func) list;
  typrog_main : ident;
}

let expr_type (e: typed_expr): ty =
  snd e

let type_of_retid_opt ty_idents id_opt =
  (Option.fold
     ~none:(Tbase Tvoid)
     ~some:(fun v -> IdentMap.find v ty_idents)
     id_opt)

(* ret, args *)
let type_of_builtin ret_ty args_ty = function
  | EF_putchar -> (Tbase Tvoid, [Tbase Tint8])
  | EF_malloc ->
    match ret_ty, args_ty with
    | Tptr _, [Tbase (Tint16|Tint8)] -> (ret_ty, args_ty)
    | _ -> die "wrong return or argument types for malloc"

let find_id id map =
  match IdentMap.find_opt id map with
  | None -> die "Unbound identifier %s" id
  | Some res -> res

let rec type_expr' ty_idents (e: expr): typed_expr =
  match e with
  | Evar v -> Evar v, find_id v ty_idents
  | Eaddr v -> Eaddr v, Tptr (find_id v ty_idents)
  | Econst (C8 x) -> Econst (C8 x), Tbase Tint8
  | Econst (C16 x) -> Econst (C16 x), Tbase Tint16
  | Ebinop (op, e1, e2) ->
    let te1, ty1 = type_expr ty_idents e1 in
    let te2, ty2 = type_expr ty_idents e2 in
    let ret_ty =
      begin match op with
      | Oadd ->
        begin match ty1, ty2 with
        | Tptr _, Tptr _ -> die "cannot add pointers"
        | Tptr pty, Tbase (Tint8 | Tint16) | Tbase (Tint8 | Tint16), Tptr pty ->
          Tptr pty
        | Tptr _, ty | ty, Tptr _ ->
          die "wrong type for pointer offset: %a" pp_ty ty
        | Tbase (Tint8|Tint16), Tbase (Tint8|Tint16) when ty1 = ty2 -> ty1
        | _, _ ->
            die "incompatible types for +: %a and %a" pp_ty ty1 pp_ty ty2
        end
      | Osub ->
        begin match ty1, ty2 with
        | Tptr _, Tptr _ -> (* ptrdiff, in bytes *) Tbase Tint16
        | Tptr pty, Tbase (Tint8 | Tint16) ->
          Tptr pty
        | _, Tptr _ -> die "cannot subtract a pointer to a non-pointer"
        | Tptr _, ty -> die "wrong type for pointer subtraction: %a" pp_ty ty
        | Tbase (Tint8|Tint16), Tbase (Tint8|Tint16) when ty1 = ty2 -> ty1
        | _, _ ->
            die "incompatible types for -: %a and %a" pp_ty ty1 pp_ty ty2
        end
      | Odiv | Omul | Oand | Oor | Oxor ->
        begin match ty1, ty2 with
        | Tbase (Tint8|Tint16), Tbase (Tint8|Tint16) when ty1 = ty2 -> ty1
        | _, _ -> die "invalid types for %s: %a and %a"
                    (string_of_op op) pp_ty ty1 pp_ty ty2
        end
      | Ocmp _ ->
        begin match ty1, ty2 with
        | Tbase (Tint8|Tint16), Tbase (Tint8|Tint16) when ty1 = ty2 ->
          Tbase Tint8
        | Tptr _, Tptr _
        | Tptr _, Tbase Tint16 | Tbase Tint16, Tptr _ -> Tbase Tint8
        | _, _ -> die "invalid types for %s: %a and %a"
                    (string_of_op op) pp_ty ty1 pp_ty ty2
        end
      end
    in
    Ebinop (op, (te1, ty1), (te2, ty2)), ret_ty
  | Eload e ->
    let te, ty = type_expr ty_idents e in
    begin match ty with
    | Tptr pty ->
      if pty = Tbase Tvoid then die "cannot load from a void pointer";
      Eload (te, ty), pty
    | _ -> die "%a has type %a but was expected of a pointer type"
             pp_expr e pp_ty ty
    end
  | Ecast (e, to_ty) ->
    if to_ty = Tbase Tvoid then die "cannot cast to void";
    let te = type_expr ty_idents e in
    Ecast (te, to_ty), to_ty

and type_expr ty_idents e =
  let te, ty = type_expr' ty_idents e in
  assert (ty <> Tbase Tvoid);
  te, ty


(* used both for function calls and calls to builtins *)
let typecheck_call ty_idents fname ret_ty args_ty ret_id_opt tes =
  begin match ret_ty, ret_id_opt with
  | Tbase Tvoid, Some _ ->
    die "call to %s: cannot bind result of function returning void" fname
  | _, None -> () (* ok to ignore result *)
  | _, Some rid ->
    let rid_ty = find_id rid ty_idents in
    if ret_ty <> rid_ty then
      die "call to %s: wrong return type: function returns a %a but expected %a"
        fname pp_ty ret_ty pp_ty rid_ty
  end;
  if List.length tes <> List.length args_ty then
    die "call to %s: wrong number of arguments (expected %d)" fname
      (List.length args_ty);
  List.iter2 (fun arg_ty (_, ety) ->
    if arg_ty <> ety then
      die "call to %s: argument type mismatch, got %a but expected %a" fname
        pp_ty ety pp_ty arg_ty
  ) args_ty tes

let rec type_stmt ty_funs ty_idents (stmt: stmt): typed_stmt =
  match stmt with
  | Sskip -> Sskip

  | Sassign (v, e) ->
    let _, ty as te = type_expr ty_idents e in
    let vty = find_id v ty_idents in
    if vty <> ty then
      die "wrong type when assigning to %s: got %a, expected %a"
        v pp_ty ty pp_ty vty;
    Sassign (v, te)

  | Sstore (e1, e2) ->
    let _, ty1 as te1 = type_expr ty_idents e1 in
    let _, ty2 as te2 = type_expr ty_idents e2 in
    begin match ty1 with
    | Tptr (Tbase Tvoid) -> die "cannot store to a void pointer"
    | Tptr pty ->
      if pty <> ty2 then
        die "type mismatch when storing: lhs has type %a, rhs has type %a"
          pp_ty ty1 pp_ty ty2
    | _ ->
      die "cannot store: lhs has type %a but must be a pointer" pp_ty ty1
    end;
    Sstore (te1, te2)

  | Scall (retid, fname, es) ->
    let fun_ret_ty, fun_args_ty = find_id fname ty_funs in
    let tes = List.map (type_expr ty_idents) es in
    typecheck_call ty_idents fname fun_ret_ty fun_args_ty retid tes;
    Scall (retid, fname, tes)

  | Sbuiltin (retid, ef, es) ->
    let tes = List.map (type_expr ty_idents) es in
    let ret_ty, args_ty =
      type_of_builtin
        (type_of_retid_opt ty_idents retid)
        (List.map snd tes)
        ef
    in
    typecheck_call ty_idents (string_of_builtin ef) ret_ty args_ty retid tes;
    Sbuiltin (retid, ef, tes)

  | Sseq (s1, s2) ->
    let ts1 = type_stmt ty_funs ty_idents s1 in
    let ts2 = type_stmt ty_funs ty_idents s2 in
    Sseq (ts1, ts2)

  | Sifthenelse (econd, s1, s2) ->
    let _, tycond as tecond = type_expr ty_idents econd in
    if tycond <> Tbase Tint8 then
      die "wrong type for a if condition: got %a, expected %a"
        pp_ty tycond pp_ty (Tbase Tint8);
    let ts1 = type_stmt ty_funs ty_idents s1 in
    let ts2 = type_stmt ty_funs ty_idents s2 in
    Sifthenelse (tecond, ts1, ts2)

  | Sloop (econd, sbody) ->
    let _, tycond as tecond = type_expr ty_idents econd in
    if tycond <> Tbase Tint8 then
      die "wrong type for a loop condition: got %a, expected %a"
        pp_ty tycond pp_ty (Tbase Tint8);
    let tsbody = type_stmt ty_funs ty_idents sbody in
    Sloop (tecond, tsbody)

let type_func ty_funs fname (f: func): typed_func =
  List.iter (fun (v, ty) ->
    if ty = Tbase Tvoid then
      die "fname: illegal parameter %s of type void" fname v
  ) f.fn_params;
  List.iter (fun (v, ty) ->
    if ty = Tbase Tvoid then
      die "fname: illegal local variable %s of type void" fname v
  ) f.fn_vars;

  let tfn_params, tfn_params_ty = List.split f.fn_params in
  let tymap_of_idents ids =
    List.fold_left (fun m (id, ty) ->
      IdentMap.add id ty m
    ) IdentMap.empty ids
  in
  let ty_params = tymap_of_idents f.fn_params in
  let ty_vars = tymap_of_idents f.fn_vars in
  (* vars shadow params *)
  let tfn_idents_ty =
    IdentMap.union (fun _ v _ -> Some v)
      ty_vars ty_params
  in
  let tfn_body = type_stmt ty_funs tfn_idents_ty f.fn_body in
  let tfn_ret = Option.map (type_expr tfn_idents_ty) f.fn_ret in
  let tfn_ret_ty = f.fn_ret_ty in

  begin match tfn_ret, tfn_ret_ty with
  | None, Tbase Tvoid -> ()
  | None, _ ->
    die "%s: non-void return type but empty return expression" fname
  | Some (_, rty), ty ->
    if rty <> ty then
      die "%s: wrong return type: returning %a but expected %a" fname
        pp_ty rty pp_ty ty
  end;

  { tfn_params; tfn_params_ty;
    tfn_vars = List.map fst f.fn_vars;
    tfn_idents_ty;
    tfn_body;
    tfn_ret; tfn_ret_ty }

let type_program (p: program): typed_program =
 let ty_funs = List.fold_left (fun ty_funs (fname, f) ->
    IdentMap.add fname (f.fn_ret_ty, List.map snd f.fn_params) ty_funs
  ) IdentMap.empty p.prog_defs
  in
  let typrog_defs = List.map (fun (fname, f) ->
    (fname, type_func ty_funs fname f)
  ) p.prog_defs
  in
  { typrog_defs; typrog_main = p.prog_main }
