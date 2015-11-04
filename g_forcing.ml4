DECLARE PLUGIN "forcing"

TACTIC EXTEND force
| [ "force" constr(obj) constr(hom) constr(c) ] -> [ assert false ]
END
