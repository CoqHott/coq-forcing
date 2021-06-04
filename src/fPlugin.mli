open Names
open Libnames
open Proofview

val force_tac : FTranslate.category -> Constr.t -> unit tactic

val force_translate : (reference * reference) -> reference -> Id.t list option -> unit

val force_implement : (reference * reference) -> Id.t -> Constrexpr.constr_expr -> Id.t option -> Constrexpr.constr_expr option -> unit
