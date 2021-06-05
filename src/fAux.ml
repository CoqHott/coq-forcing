(** Utilities *)

let clos_norm_flags flgs env t =
  CClosure.norm_val
    (CClosure.create_clos_infos flgs env)
    (CClosure.create_tab ())
    (CClosure.inject t)
