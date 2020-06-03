open RedTT_Core

type filepath = string
type selector = string list

val selector_to_stem : stem : filepath -> selector -> filepath
val red_to_stem : filepath -> filepath
val stem_to_red : filepath -> filepath
val stem_to_rot : filepath -> filepath

val pp_selector : selector Pp.t0
