open Globnames

type category = {
  cat_obj : Constr.t;
  (** Objects. Must be a closed term of type [Type]. *)
  cat_hom : Constr.t;
  (** Morphisms. Must be a closed term of type [cat_obj -> cat_obj -> Type]. *)
}

type translator = global_reference Refmap.t

val translate : translator -> category ->
  Environ.env -> Evd.evar_map -> Constr.t -> Evd.evar_map * Constr.t
