open Names
open Term
open Environ
open Globnames

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

let apply_global env sigma gr u fctx =
  (** FIXME *)
  let p' =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  let (sigma, c) = Evd.fresh_global env sigma p' in
  let last = last_condition fctx in
  (sigma, mkApp (c, [| mkRel last |]))

(** Forcing translation core *)

let rec translate_aux env fctx sigma c = match kind_of_term c with
| Rel n ->
  let p = mkRel (last_condition fctx) in
  let f = morphism_var n fctx in
  let m = get_var_shift n fctx in
  let ans = mkApp (mkRel m, [| p; f |]) in
  (sigma, ans)
| Var id -> assert false
| Sort s ->
  let (ext0, fctx) = extend fctx in
  let (ext, fctx) = extend fctx in
  let (sigma, s') = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
  let tpe = it_mkProd_or_LetIn (mkSort s') ext in
  let lam = it_mkLambda_or_LetIn tpe ext0 in
  (sigma, lam)
| Cast (c, k, t) -> assert false
| Prod (na, t, u) ->
  let (ext0, fctx) = extend fctx in
  (** Translation of t *)
  let (ext, tfctx) = extend fctx in
  let (sigma, t_) = translate_type env tfctx sigma t in
  let t_ = it_mkProd_or_LetIn t_ ext in
  (** Translation of u *)
  let ufctx = add_variable fctx in
  let (sigma, u_) = translate_type env ufctx sigma u in
  (** Result *)
  let ans = mkProd (na, t_, u_) in
  let lam = it_mkLambda_or_LetIn ans ext0 in
  (sigma, lam)
| Lambda (na, t, u) ->
  (** Translation of t *)
  let (ext, tfctx) = extend fctx in
  let (sigma, t_) = translate_type env tfctx sigma t in
  let t_ = it_mkProd_or_LetIn t_ ext in
  (** Translation of u *)
  let ufctx = add_variable fctx in
  let (sigma, u_) = translate_aux env ufctx sigma u in
  let ans = mkLambda (na, t_, u_) in
  (sigma, ans)
| LetIn (na, c, t, u) -> assert false
| App (t, args) ->
  let (sigma, t_) = translate_aux env fctx sigma t in
  let (ext, ufctx) = extend fctx in
  let fold sigma u =
    let (sigma, u_) = translate_aux env ufctx sigma u in
    let u_ = it_mkLambda_or_LetIn u_ ext in
    (sigma, u_)
  in
  let (sigma, args_) = CList.fold_map fold sigma (Array.to_list args) in
  (sigma, mkApp (t_, Array.of_list args_))
| Const (p, u) ->
  apply_global env sigma (ConstRef p) u fctx
| Ind pi -> assert false
| Construct pc -> assert false
| Case (ci, c, r, p) -> assert false
| Fix f -> assert false
| CoFix f -> assert false
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false

and translate_type env fctx sigma t =
  let (sigma, t_) = translate_aux env fctx sigma t in
  let last = mkRel (last_condition fctx) in
  let t_ = mkApp (t_, [| last; refl fctx.category last |]) in
  (sigma, t_)

let translate translator cat env sigma c =
  let empty = { context = []; category = cat; translator; } in
  let (sigma, c) = translate_aux env empty sigma c in
  (sigma, mkLambda (pos_name, cat.cat_obj, c))

let translate_type translator cat env sigma c =
  let empty = { context = []; category = cat; translator; } in
  let (sigma, c) = translate_aux env empty sigma c in
  let c = mkApp (c, [| mkRel 1; refl cat (mkRel 1) |]) in
  (sigma, mkProd (pos_name, cat.cat_obj, c))
