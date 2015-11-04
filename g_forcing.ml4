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
    let concl = Proofview.Goal.concl gl in
    let (sigma, ans) = FTranslate.translate env sigma cat concl in
    Proofview.Unsafe.tclEVARS sigma <*> Tactics.exact_check ans
  end

TACTIC EXTEND force
| [ "force" constr(obj) constr(hom) constr(c) ] -> [ force_tac obj hom c ]
END
