DECLARE PLUGIN "forcing"

TACTIC EXTEND force
| [ "force" constr(c) ] -> [
  FPlugin.force_tac c
]
END

VERNAC COMMAND EXTEND ForcingTranslation CLASSIFIED AS SIDEFF
| [ "Forcing" "Translate" global(gr) ] ->
  [ FPlugin.force_translate gr None ]
| [ "Forcing" "Translate" global(gr) "as" ident(id) ] ->
  [ FPlugin.force_translate gr (Some id) ]
END

let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND ForcingImplementation CLASSIFIED BY classify_impl
| [ "Forcing" "Definition" ident(id) ":" lconstr(typ) ] ->
  [ FPlugin.force_implement id typ None ]
| [ "Forcing" "Definition" ident(id) ":" lconstr(typ) "as" ident(id') ] ->
  [ FPlugin.force_implement id typ (Some id') ]
END
