type ('a, 'b) t

val empty: ('a, 'b) t

val get_term_var: string -> ('a, 'b) t -> 'a
val get_typ_var: string -> ('a, 'b) t -> 'b

val add_term_var: string -> 'a -> ('a, 'b) t -> ('a, 'b) t
val add_typ_var: string -> 'b -> ('a, 'b) t -> ('a, 'b) t

