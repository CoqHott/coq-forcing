DECLARE PLUGIN "forcing"

TACTIC EXTEND force
| [ "force" constr(obj) constr(hom) constr(c) ] -> [ FPlugin.force_tac obj hom c ]
END
