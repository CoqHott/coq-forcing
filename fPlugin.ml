open Names
open Term
open Proofview.Notations

(** Utilities *)

let translate_name kn =
  let label = KerName.label kn in
  let label = Label.to_string label in
  Id.of_string ("ℱ" ^ label)

(** Tactic *)

let empty_translator = Globnames.Refmap.empty

let force_tac obj hom c =
  let cat = {
    FTranslate.cat_obj = obj;
    FTranslate.cat_hom = hom;
  } in
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, ans) = FTranslate.translate empty_translator cat env sigma c in
    Pp.msg_notice (Termops.print_constr c);
    Pp.msg_notice (Termops.print_constr ans);
    Proofview.Unsafe.tclEVARS sigma <*>
    Tactics.letin_tac None Names.Name.Anonymous ans None Locusops.allHyps
  end
