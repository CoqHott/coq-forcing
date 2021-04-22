open Globnames

type category = {
  cat_obj : Constr.t;
  (** Objects. Must be a closed term of type [Type]. *)
  cat_hom : Constr.t;
  (** Morphisms. Must be a closed term of type [cat_obj -> cat_obj -> Type]. *)
}

exception MissingGlobal of global_reference

type translator = global_reference Refmap.t

val hom : category -> Constr.constr -> Constr.constr -> Term.types

val translate : ?toplevel:bool ->  ?lift:int -> translator -> category ->
  Environ.env -> Evd.evar_map -> Constr.t -> Evd.evar_map * Constr.t

val translate_type : ?toplevel:bool -> ?lift:int -> translator -> category ->
  Environ.env -> Evd.evar_map -> Constr.t -> Evd.evar_map * Constr.t

val translate_context : ?toplevel:bool -> ?lift:int -> translator -> category ->
  Environ.env -> Evd.evar_map -> Context.Rel.t -> Evd.evar_map * Context.Rel.t
