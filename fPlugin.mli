open Names
open Libnames
open Proofview

val force_tac : Constr.t -> unit tactic

val force_translate : reference -> Id.t option -> unit

val force_implement : Id.t -> Constrexpr.constr_expr -> Id.t option -> unit
