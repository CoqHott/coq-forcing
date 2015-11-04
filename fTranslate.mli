type category = {
  cat_obj : Constr.t;
  (** Objects. Must be a closed term of type [Type]. *)
  cat_hom : Constr.t;
  (** Morphisms. Must be a closed term of type [cat_obj -> cat_obj -> Type]. *)
}

val translate : Environ.env -> Evd.evar_map -> category -> Constr.t -> Evd.evar_map * Constr.t
