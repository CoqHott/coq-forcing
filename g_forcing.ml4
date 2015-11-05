DECLARE PLUGIN "forcing"

TACTIC EXTEND force
| [ "force" constr(obj) constr(hom) constr(c) ] -> [
  let cat = {
    FTranslate.cat_obj = obj;
    FTranslate.cat_hom = hom;
  } in
  FPlugin.force_tac cat c
]
END

VERNAC COMMAND EXTEND ForcingTranslation CLASSIFIED AS SIDEFF
| [ "Forcing" "Translate" global(gr) "using" global(obj) global(hom) ] ->
  [ FPlugin.force_translate (obj, hom) gr None ]
| [ "Forcing" "Translate" global(gr) "as" ident(id) "using" global(obj) global(hom) ] ->
  [ FPlugin.force_translate (obj, hom) gr (Some id) ]
END
