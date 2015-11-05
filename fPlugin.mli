open Names
open Libnames
open Proofview

val force_tac : FTranslate.category -> Constr.t -> unit tactic

val force_translate : (reference * reference) -> reference -> Id.t option -> unit
