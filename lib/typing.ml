open Common
open Types
open Lang

let die fmt = Common.die ~where:"typing" fmt

let type_of_expr (e: expr): ty =
  snd e

let type_of_ident genv lenv v =
  match IdentMap.find_opt v lenv with
  | Some ty -> ty
  | None ->
    match IdentMap.find_opt v genv.genv_globs with
    | Some ty -> ty
    | None -> die "Unbound identifier: %s" v

let type_of_func genv f =
  match IdentMap.find_opt f genv.genv_funs with
  | Some ty -> ty
  | None -> die "Unbound function: %s" f

let evar genv lenv v : expr =
  Evar v, type_of_ident genv lenv v

let eaddr genv lenv v : expr =
  Eaddr v, Tptr (type_of_ident genv lenv v)

let econst c : expr =
  Econst c, type_of_const c

let ebinop op (e1: expr) (e2: expr): expr =
  let ty1, ty2 = type_of_expr e1, type_of_expr e2 in
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
  Ebinop (op, e1, e2), ret_ty

let eload (e: expr) : expr =
  let ty = type_of_expr e in
  begin match ty with
  | Tptr pty ->
    if pty = Tbase Tvoid then die "cannot load from a void pointer";
    Eload e, pty
  | _ -> die "%a has type %a but was expected of a pointer type"
           pp_expr e pp_ty ty
  end

let ecast (e: expr) to_ty : expr =
  if to_ty = Tbase Tvoid then die "cannot cast to void";
  Ecast (e, to_ty), to_ty

(* ret, args *)
let type_of_builtin args_ty = function
  | EF_putchar -> (Tbase Tvoid, [Tbase Tint8])
  | EF_malloc ->
    begin match args_ty with
    | [Tbase (Tint16|Tint8)] -> (Tptr (Tbase Tvoid), args_ty)
    | _ -> die "malloc: wrong return or argument types"
    end
  | EF_out ->
    begin match args_ty with
    | [_; Tbase Tint8] -> (Tbase Tvoid, args_ty)
    | _ -> die "out: wrong number of arguments or argument types"
    end
  | EF_in8 ->
    begin match args_ty with
    | [Tbase Tint8] -> (Tbase Tint8, args_ty)
    | _ -> die "out: wrong number of arguments"
    end
  | EF_in16 ->
    begin match args_ty with
    | [Tbase Tint8] -> (Tbase Tint16, args_ty)
    | _ -> die "out: wrong number of arguments"
    end

(* used both for function calls and calls to builtins *)
let typecheck_call fname(*for printing*) args_ty (es: expr list) =
  if List.length es <> List.length args_ty then
    die "call to %s: wrong number of arguments (expected %d)" fname
      (List.length args_ty);
  List.iter2 (fun arg_ty (_, ety) ->
    if arg_ty <> ety then
      die "call to %s: argument type mismatch, got %a but expected %a" fname
        pp_ty ety pp_ty arg_ty
  ) args_ty es

let ecall genv f (es: expr list) : expr =
  let (f_ret_ty, f_args_ty) = type_of_func genv f in
  typecheck_call f f_args_ty es;
  Ecall (f, es), f_ret_ty

let ebuiltin ef (es: expr list) : expr =
  let (ret_ty, args_ty) = type_of_builtin (List.map type_of_expr es) ef in
  typecheck_call (string_of_builtin ef) args_ty es;
  Ebuiltin (ef, es), ret_ty

let sskip : stmt = Sskip
let sdo (e: expr) : stmt =
  (* allow throwing away the result *)
  Sdo e

let sassign genv lenv v e =
  let ty = type_of_expr e in
  let vty = type_of_ident genv lenv v in
  if vty <> ty then
    die "wrong type when assigning to %s: got %a, expected %a"
      v pp_ty ty pp_ty vty;
  Sassign (v, e)

let sstore e1 e2 =
  let ty1 = type_of_expr e1 in
  let ty2 = type_of_expr e2 in
  begin match ty1 with
  | Tptr (Tbase Tvoid) -> die "cannot store to a void pointer"
  | Tptr pty ->
    if pty <> ty2 then
      die "type mismatch when storing: lhs has type %a, rhs has type %a"
        pp_ty ty1 pp_ty ty2
  | _ ->
    die "cannot store: lhs has type %a but must be a pointer" pp_ty ty1
  end;
  Sstore (e1, e2)

let sseq s1 s2 = Sseq (s1, s2)

let sifthenelse econd s1 s2 =
  let tycond = type_of_expr econd in
  if tycond <> Tbase Tint8 then
    die "wrong type for a if condition: got %a, expected %a"
      pp_ty tycond pp_ty (Tbase Tint8);
  Sifthenelse (econd, s1, s2)

let sloop econd sbody =
  let tycond = type_of_expr econd in
  if tycond <> Tbase Tint8 then
    die "wrong type for a loop condition: got %a, expected %a"
      pp_ty tycond pp_ty (Tbase Tint8);
  Sloop (econd, sbody)

let build_genv (proto_decls :
                  [ `Glob of ty * ident
                  | `Fun of ty * ident * (ident * ty) list ] list)
  =
  (* check for duplicated global decls / function decls *)
  begin
    let sorted_decls =
      List.map (function
        | `Glob (_, s) -> (`Glob, s)
        | `Fun (_, s, _) -> (`Fun, s)
      ) proto_decls |> List.sort compare
    in
    let rec check_dup = function
      | [] | [_] -> ()
      | (k, name) :: (k', name') :: ns ->
        if k = k' && name = name' then
          die "%s %s is defined twice"
            (match k with `Glob -> "Global" | `Fun -> "Function") name;
        check_dup ((k', name') :: ns)
    in
    check_dup sorted_decls
  end;
  List.fold_left (fun (genv: genv) decl ->
    match decl with
    | `Glob (ty, gname) ->
      if ty = Tbase Tvoid then die "Global %s: type cannot be void" gname;
      { genv with genv_globs = IdentMap.add gname ty genv.genv_globs }
    | `Fun (ret_ty, fname, params) ->
      List.iter (fun (v, ty) ->
        if ty = Tbase Tvoid then
          die "%s: illegal parameter %s of type void" fname v
      ) params;
      { genv with
        genv_funs = IdentMap.add fname (ret_ty, List.map snd params) genv.genv_funs }
  ) { genv_globs = IdentMap.empty; genv_funs = IdentMap.empty } proto_decls

let build_lenv fname (params: (ident * ty) list) (vars: (ident * ty) list) : lenv =
  (* already checked that parameters are non-void when constructing genv *)
  List.iter (fun (v, ty) ->
    if ty = Tbase Tvoid then
      die "%s: illegal local variable %s of type void" fname v
  ) vars;
  let ty_params = IdentMap.of_seq (List.to_seq params) in
  let ty_vars = IdentMap.of_seq (List.to_seq vars) in
  (* vars shadow params *)
  IdentMap.union (fun _ v _ -> Some v)
    ty_vars ty_params

let func genv lenv fname
    (params: (ident * ty) list) (vars: (ident * ty) list) (body: stmt)
    (ret: expr option) : func
  =
  let ret_ty, _ = type_of_func genv fname in
  begin match ret, ret_ty with
  | None, Tbase Tvoid -> ()
  | None, _ ->
    die "%s: non-void return type but empty return expression" fname
  | Some (_, rty), ty ->
    if rty <> ty then
      die "%s: wrong return type: returning %a but expected %a" fname
        pp_ty rty pp_ty ty
  end;
  { fn_lenv = lenv; fn_params = params; fn_vars = vars;
    fn_body = body; fn_ret = ret; fn_ret_ty = ret_ty }

let glob genv gname (init: glob_init option) : glob =
  let ty = IdentMap.find gname genv.genv_globs in
  match init with
  | None -> { gl_ty = ty; gl_init = None }
  | Some init ->
    begin match init with
    | Gconst c ->
      if ty <> type_of_const c then
        die "Global %s: initial value has type %a but was expected of type %a" gname
          pp_ty (type_of_const c) pp_ty ty;
    | Garray [] ->
      begin match ty with
      | Tptr _ -> ()
      | _ -> die "Global %s must be of pointer type" gname
      end
    | Garray (c::cs) ->
      let c_ty = type_of_const c in
      if not (List.for_all (fun c' -> type_of_const c' = c_ty) cs) then
        die "Heterogeneous constant array for global %s" gname;
      if ty <> Tptr c_ty then
        die "Global %s has type %a but was expected of type %a" gname
          pp_ty ty pp_ty (Tptr c_ty);
    end;
    { gl_ty = ty; gl_init = Some init }
