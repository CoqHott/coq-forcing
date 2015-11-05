open Names
open Term
open Decl_kinds
open Proofview.Notations

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string ("ℱ" ^ id)

(** Tactic *)

let empty_translator = Globnames.Refmap.empty

let force_tac cat c =
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, ans) = FTranslate.translate empty_translator cat env sigma c in
    Proofview.Unsafe.tclEVARS sigma <*>
    Tactics.letin_tac None Names.Name.Anonymous ans None Locusops.allHyps
  end

let force_solve cat c =
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, ans) = FTranslate.translate empty_translator cat env sigma c in
    Proofview.Unsafe.tclEVARS sigma <*>
    Tactics.exact_check ans
  end

let force_translate (obj, hom) gr idopt =
  let gr = Nametab.global gr in
  let obj = Universes.constr_of_global (Nametab.global obj) in
  let hom = Universes.constr_of_global (Nametab.global hom) in
  let cat = {
    FTranslate.cat_obj = obj;
    FTranslate.cat_hom = hom;
  } in
  (** Translate the type *)
  let sigma = Evd.empty in
  let typ = Universes.unsafe_type_of_global gr in
  let env = Global.env () in
  let (sigma, typ) = FTranslate.translate_type empty_translator cat env sigma typ in
  let uctx = Evd.evar_universe_context sigma in
  (** Define the term by tactic *)
  let id = match idopt with
  | None -> translate_name (Nametab.basename_of_global gr)
  | Some id -> id
  in
  let body = match gr with
  | ConstRef cst -> Option.get (Global.body_of_constant cst)
  | _ -> assert false
  in
  let tac = force_solve cat body in
  let sign = Environ.empty_named_context_val in
  let (const, safe, uctx) = Pfedit.build_constant_by_tactic id uctx sign typ tac in
  let cd = Entries.DefinitionEntry const in
  let decl = (cd, IsProof Lemma) in
  let _ = Declare.declare_constant id decl in
  ()
