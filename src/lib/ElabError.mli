include module type of ElabErrorData.Data

val pp : Format.formatter -> t -> unit

exception ElabError of t
