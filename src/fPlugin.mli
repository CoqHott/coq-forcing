open Names
open Libnames
open Proofview

val force_tac : (EConstr.t * EConstr.t) -> EConstr.t -> unit tactic

val force_translate : (qualid * qualid) -> qualid -> Id.t list option -> unit

val force_implement : (qualid * qualid) -> Id.t -> Constrexpr.constr_expr -> Id.t option -> unit
