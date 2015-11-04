open Names
open Term
open Environ

type category = {
  cat_obj : Constr.t;
  (** Objects. Must be of type [Type]. *)
  cat_hom : Constr.t;
  (** Morphisms. Must be of type [cat_obj -> cat_obj -> Type]. *)
}

(** Yoneda embedding *)

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
  bool (** Is the forcing condition linked to a variable? *) *
  Constr.t (** Level of the forcing condition *) *
  Constr.t (** Morphism attached to the forcing condition *)

type forcing_context = (bool * Constr.t * Constr.t) list

let pos_name = Name (Id.of_string "p")
let hom_name = Name (Id.of_string "α")

let dummy = mkProp

(** We assume that there is a hidden topmost variable [p : Obj] in the context *)

let rec morphism_var n ctx fctx = match ctx, fctx with
| _ -> dummy

let last_condition ctx fctx = match ctx, fctx with
| _ -> 1

let rec translate_aux env fctx sigma cat c = match kind_of_term c with
| Rel n ->
  let ctx = Environ.rel_context env in
  let p = mkRel (last_condition ctx fctx) in
  let f = morphism_var n ctx fctx in
  let ans = mkApp (mkRel n, [| p; f |]) in
  (sigma, ans)
| Var id -> assert false
| Sort s ->
  let (sigma, s') = Evd.new_sort_variable Evd.univ_flexible sigma in
  let tpe' = mkArrow (hom cat (mkRel 3) (mkRel 1)) (mkSort s') in
  let tpe = mkProd (pos_name, cat.cat_obj, tpe') in
  let lam = mkLambda (hom_name, hom cat dummy (mkRel 2), tpe) in
  (sigma, mkLambda (pos_name, cat.cat_obj, lam))
| Cast (c, k, t) -> assert false
| Prod (na, t, u) -> (sigma, dummy)
| Lambda (na, t, u) ->
  let (sigma, t_) = translate_aux env fctx sigma cat t in
  let uenv = push_rel (na, None, t_) env in
  let ufctx = (true, dummy, dummy) :: fctx in
  let (sigma, u_) = translate_aux uenv ufctx sigma cat u in
  let ans = mkLambda (na, t_, u_) in
  (sigma, ans)
| LetIn (na, c, t, u) -> assert false
| App (t, args) ->
  let (sigma, t_) = translate_aux env fctx sigma cat t in
  let fold sigma u = (sigma, u) in
  let (sigma, args_) = CList.fold_map fold sigma (Array.to_list args) in
  (sigma, mkApp (t_, Array.of_list args_))
| Const pc -> assert false
| Ind pi -> assert false
| Construct pc -> assert false
| Case (ci, c, r, p) -> assert false
| Fix f -> assert false
| CoFix f -> assert false
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false

let translate env sigma cat c =
  let (sigma, c) = translate_aux env [] sigma cat c in
  (sigma, mkLambda (pos_name, cat.cat_obj, c))
