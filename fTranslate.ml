open Names
open Term
open Environ
open Globnames
open Pp

type translator = global_reference Refmap.t
exception MissingGlobal of global_reference

(** Yoneda embedding *)

type category = {
  cat_obj : Constr.t;
  (** Objects. Must be of type [Type]. *)
  cat_hom : Constr.t;
  (** Morphisms. Must be of type [cat_obj -> cat_obj -> Type]. *)
}

let obj_name = Name (Id.of_string "R")
let knt_name = Name (Id.of_string "k")

let hom cat a b =
  let lft = mkApp (cat.cat_hom, [| Vars.lift 1 b; mkRel 1 |]) in
  let rgt = mkApp (cat.cat_hom, [| Vars.lift 2 a; mkRel 2 |]) in
  let arr = mkArrow lft rgt in
  mkProd (obj_name, cat.cat_obj, arr)

let refl cat a =
  let hom = mkApp (cat.cat_hom, [| Vars.lift 1 a; mkRel 1 |]) in
  let lam = mkLambda (knt_name, hom, mkRel 1) in
  mkLambda (obj_name, cat.cat_obj, lam)

let trns cat a b c f g =
  let hom = mkApp (cat.cat_hom, [| Vars.lift 1 c; mkRel 1 |]) in
  let app = mkApp (Vars.lift 2 g, [| mkRel 2; mkRel 1 |]) in
  let app' = mkApp (Vars.lift 2 f, [| mkRel 2; app |]) in
  let lam = mkLambda (knt_name, hom, app') in
  mkLambda (obj_name, cat.cat_obj, lam)

(** Optimization of cuts *)

let mkOptApp (t, args) =
  let len = Array.length args in
  try
    let (_, t) = Term.decompose_lam_n len t in
    Vars.substl (CArray.rev_to_list args) t
  with _ ->
    mkApp (t, args)

(** Forcing translation *)

type forcing_condition =
| Variable
| Lift

type forcing_context = {
  context : forcing_condition list;
  (** Forcing contexts are flagging variables of the rel_context in the same
    order. We statically know that variables coming from the introduction of
    a forcing condition come by pairs: the first one is a level, the second one
    a morphism. There is therefore only [Lift] condition for such pairs. *)
  category : category;
  (** Underlying category *)
  translator : translator;
  (** A map associating to all source constant a forced constant *)
}

(** We assume that there is a hidden topmost variable [p : Obj] in the context *)

let pos_name = Name (Id.of_string "p")
let hom_name = Name (Id.of_string "α")

let dummy = mkProp

let last_condition fctx =
  let rec last fctx = match fctx with
  | [] -> 1
  | Variable :: fctx -> 1 + last fctx
  | Lift :: fctx -> 2
  in
  last fctx.context

let gather_morphisms n fctx =
  let rec gather i n fctx =
    if n = 0 then []
    else match fctx with
    | [] -> []
    | Variable :: fctx -> gather (i + 1) (n - 1) fctx
    | Lift :: fctx -> i :: gather (i + 2) n fctx
  in
  gather 1 n fctx.context

let morphism_var n fctx =
  let morphs = gather_morphisms n fctx in
  let last = mkRel (last_condition fctx) in
  let fold accu i =
    trns fctx.category dummy dummy last (mkRel i) accu
  in
  List.fold_left fold (refl fctx.category last) morphs

let get_var_shift n fctx =
  let rec get n fctx =
    if n = 0 then 0
    else match fctx with
    | [] -> n
    | Variable :: fctx -> 1 + get (n - 1) fctx
    | Lift :: fctx -> 2 + get n fctx
  in
  get n fctx.context

let extend fctx =
  let cat = fctx.category in
  let last = last_condition fctx in
  let ext = [(hom_name, None, hom cat (mkRel (1 + last)) (mkRel 1)); (pos_name, None, cat.cat_obj)] in
  (ext, { fctx with context = Lift :: fctx.context })

let add_variable fctx =
  { fctx with context = Variable :: fctx.context }

(** Handling of globals *) 

let translate_var fctx n =
  let p = mkRel (last_condition fctx) in
  let f = morphism_var n fctx in
  let m = get_var_shift n fctx in
  mkApp (mkRel m, [| p; f |])

(* let lift_decl i (na, b, t) = (na, Option.map (Vars.lift i) b, Vars.lift i t) *)

let apply_global env sigma gr u fctx =
  (** FIXME *)
  let p' =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  let (sigma, c) = Evd.fresh_global env sigma p' in
  let last = last_condition fctx in
  match gr with
  | IndRef _ ->
    let cat = fctx.category in
    let (_, oib) = Inductive.lookup_mind_specif env (fst (destInd c)) in
    (** First parameter is the toplevel forcing condition *)
    let _, paramtyp = CList.sep_last oib.mind_arity_ctxt in
    let nparams = List.length paramtyp in
    let fctx = List.fold_left (fun accu _ -> add_variable accu) fctx paramtyp in
    let (ext, fctx) = extend fctx in
    let mk_var n =
      let n = nparams - n in
      let (ext0, fctx) = extend fctx in
      let ans = translate_var fctx n in
      it_mkLambda_or_LetIn ans ext0
    in
    let params = CList.init nparams mk_var in
    let app = applist (c, mkRel (last_condition fctx) :: params) in
    let map_p i c = Vars.substnl_decl [mkRel (last - i)] (nparams - i - 1) c in
(*     let map_p i c = Vars.substnl_decl [mkProp] (last - i - 1) c in *)
    let paramtyp = List.mapi map_p paramtyp in
    let ans = it_mkLambda_or_LetIn app (ext @ paramtyp) in
    msg_info (Termops.print_constr ans);
    (sigma, ans)
  | _ -> (sigma, mkApp (c, [| mkRel last |]))

(** Forcing translation core *)

let rec otranslate env fctx sigma c = match kind_of_term c with
| Rel n ->
  let ans = translate_var fctx n in
  (sigma, ans)
| Sort s ->
  let (ext0, fctx) = extend fctx in
  let (ext, fctx) = extend fctx in
  let (sigma, s') =
    if Sorts.is_prop s then (sigma, Sorts.prop)
    else Evd.new_sort_variable Evd.univ_flexible_alg sigma
  in
  let sigma = Evd.set_leq_sort env sigma s s' in
  let tpe = it_mkProd_or_LetIn (mkSort s') ext in
  let lam = it_mkLambda_or_LetIn tpe ext0 in
  (sigma, lam)
| Cast (c, k, t) ->
  let (sigma, c_) = otranslate env fctx sigma c in
  let (sigma, t_) = otranslate_type env fctx sigma t in
  let ans = mkCast (c_, k, t_) in
  (sigma, ans)
| Prod (na, t, u) ->
  let (ext0, fctx) = extend fctx in
  (** Translation of t *)
  let (ext, tfctx) = extend fctx in
  let (sigma, t_) = otranslate_type env tfctx sigma t in
  let t_ = it_mkProd_or_LetIn t_ ext in
  (** Translation of u *)
  let ufctx = add_variable fctx in
  let (sigma, u_) = otranslate_type env ufctx sigma u in
  (** Result *)
  let ans = mkProd (na, t_, u_) in
  let lam = it_mkLambda_or_LetIn ans ext0 in
  (sigma, lam)
| Lambda (na, t, u) ->
  (** Translation of t *)
  let (ext, tfctx) = extend fctx in
  let (sigma, t_) = otranslate_type env tfctx sigma t in
  let t_ = it_mkProd_or_LetIn t_ ext in
  (** Translation of u *)
  let ufctx = add_variable fctx in
  let (sigma, u_) = otranslate env ufctx sigma u in
  let ans = mkLambda (na, t_, u_) in
  (sigma, ans)
| LetIn (na, c, t, u) -> assert false
| App (t, args) ->
  let (sigma, t_) = otranslate env fctx sigma t in
  let (ext, ufctx) = extend fctx in
  let fold sigma u =
    let (sigma, u_) = otranslate env ufctx sigma u in
    let u_ = it_mkLambda_or_LetIn u_ ext in
    (sigma, u_)
  in
  let (sigma, args_) = CList.fold_map fold sigma (Array.to_list args) in
  let app = mkApp (t_, Array.of_list args_) in
  (sigma, app)
| Var id ->
  apply_global env sigma (VarRef id) Univ.Instance.empty fctx
| Const (p, u) ->
  apply_global env sigma (ConstRef p) u fctx
| Ind (i, u) ->
  apply_global env sigma (IndRef i) u fctx
| Construct (c, u) ->
  apply_global env sigma (ConstructRef c) u fctx
| Case (ci, c, r, p) ->
   (* let (sigma, c_) = otranslate env fctx sigma c in *)
   (* let (sigma, r_) = otranslate_type env fctx sigma r in *)
   (* let fold sigma u = *)
   (*  let (sigma, u_) = otranslate env fctx sigma u in *)
   (*  (sigma, u_) *)
   (* in *)
   (* let (sigma, p_) = CList.fold_map fold sigma (Array.to_list p) in *)
   (* let p_ = Array.of_list p_ in *)
   (* (sigma, mkCase (ci, c_, r_, p_)) *)
   assert false
| Fix f -> assert false
| CoFix f -> assert false
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false

and otranslate_type env fctx sigma t =
  let (sigma, t_) = otranslate env fctx sigma t in
  let last = mkRel (last_condition fctx) in
  let t_ = mkOptApp (t_, [| last; refl fctx.category last |]) in
  (sigma, t_)

let empty translator cat lift env =
  let ctx = rel_context env in
  let empty = { context = []; category = cat; translator; } in
  let empty = List.fold_right (fun _ fctx -> add_variable fctx) ctx empty in
  let rec flift fctx n =
    if n = 0 then fctx
    else flift (snd (extend fctx)) (pred n)
  in
  flift empty (match lift with None -> 0 | Some n -> n)

(** The toplevel option allows to close over the topmost forcing condition *)

let translate ?(toplevel = true) ?lift translator cat env sigma c =
  let empty = empty translator cat lift env in
  let (sigma, c) = otranslate env empty sigma c in
  let ans = if toplevel then mkLambda (pos_name, cat.cat_obj, c) else c in
  (sigma, ans)

let translate_type ?(toplevel = true) ?lift translator cat env sigma c =
  let empty = empty translator cat lift env in
  let (sigma, c) = otranslate_type env empty sigma c in
  let ans = if toplevel then mkProd (pos_name, cat.cat_obj, c) else c in
  (sigma, ans)

let translate_context ?(toplevel = true) ?lift translator cat env sigma ctx =
  let empty = empty translator cat lift env in
  let fold (na, body, t) (sigma, fctx, ctx_) =
    let (sigma, body_) = match body with
    | None -> (sigma, None)
    | Some _ -> assert false
    in
    let (ext, tfctx) = extend fctx in
    let (sigma, t_) = otranslate_type env tfctx sigma t in
    let t_ = it_mkProd_or_LetIn t_ ext in
    let decl_ = (na, body_, t_) in
    let fctx = add_variable fctx in
    (sigma, fctx, decl_ :: ctx_)
  in
  let init = if toplevel then [pos_name, None, cat.cat_obj] else [] in
  let (sigma, _, ctx_) = List.fold_right fold ctx (sigma, empty, init) in
  (sigma, ctx_)
