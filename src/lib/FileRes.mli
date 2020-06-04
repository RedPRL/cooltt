type filepath = string
type selector = string list

val selector_to_stem : stem : filepath -> selector -> filepath
val cool_to_stem : filepath -> filepath
val stem_to_cool : filepath -> filepath
val stem_to_slush : filepath -> filepath

val pp_selector : selector Pp.t0
