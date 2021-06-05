open Ltac_plugin
open Stdarg
open Extraargs

DECLARE PLUGIN "forcing"

TACTIC EXTEND force
| [ "force" constr(obj) constr(hom) constr(c) ] -> [
  FPlugin.force_tac (obj,hom) c
]
END

VERNAC COMMAND EXTEND ForcingTranslation CLASSIFIED AS SIDEFF
| [ "Forcing" "Translate" global(gr) "using" global(obj) global(hom) ] ->
  [ FPlugin.force_translate (obj, hom) gr None ]
| [ "Forcing" "Translate" global(gr) "as" ne_ident_list(id) "using" global(obj) global(hom) ] ->
  [ FPlugin.force_translate (obj, hom) gr (Some id) ]
END

let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND ForcingImplementation CLASSIFIED BY classify_impl
| [ "Forcing" "Definition" ident(id) ":" lconstr(typ) "using" global(obj) global(hom) ] ->
  [ FPlugin.force_implement (obj, hom) id typ None ]
| [ "Forcing" "Definition" ident(id) ":" lconstr(typ) "as" ident(id') "using" global(obj) global(hom) ] ->
  [ FPlugin.force_implement (obj, hom) id typ (Some id') ]
END
