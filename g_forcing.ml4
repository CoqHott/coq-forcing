DECLARE PLUGIN "forcing"

open Proofview.Notations

let force_tac obj hom c =
  let cat = {
    FTranslate.cat_obj = obj;
    FTranslate.cat_hom = hom;
  } in
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, ans) = FTranslate.translate env sigma cat c in
    Pp.msg_notice (Termops.print_constr c);
    Pp.msg_notice (Termops.print_constr ans);
    Proofview.Unsafe.tclEVARS sigma <*>
    Tactics.pose_proof Names.Name.Anonymous ans
  end

TACTIC EXTEND force
| [ "force" constr(obj) constr(hom) constr(c) ] -> [ force_tac obj hom c ]
END
