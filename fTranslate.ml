open Names
open Term

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
  let hom = hom cat (Vars.lift 1 a) (mkRel 1) in
  let lam = mkLambda (knt_name, hom, mkRel 1) in
  mkLambda (obj_name, cat.cat_obj, lam)

let trns cat a b c f g =
  assert false

(** Forcing translation *)

let translate env sigma cat c =
  assert false

let rec translate_aux env sigma cat c = match kind_of_term c with
| Rel n -> assert false
| Var id -> assert false
| Sort s -> assert false
| Cast (c, k, t) -> assert false
| Prod (na, t, u) -> assert false
| Lambda (na, t, u) -> assert false
| LetIn (na, c, t, u) -> assert false
| App (t, args) -> assert false
| Const pc -> assert false
| Ind pi -> assert false
| Construct pc -> assert false
| Case (ci, c, r, p) -> assert false
| Fix f -> assert false
| CoFix f -> assert false
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false
