(** Error handling. *)

(** Categories of errors. *)
type t

(** Lexing error. *)
val lexing: t

(** Parsing error. *)
val parsing: t

(** Syntax error. *)
val syntax: t

(** Type wellformedness error. *)
val type_wf: t

(** Kind wellformedness error. *)
val kind_wf: t

(** Term wellformedness error. *)
val term_wf: t

(** Program wellformedness error. *)
val prog_wf: t

(** Type wellformedness error. *)
val subtype: t

(** Kind wellformedness error. *)
val subkind: t

(** Zipping of environment error. *)
val zip: t

(** Purity of environment error. *)
val purity: t

(** Misuse of a type variable error. *)
val misused_typ_var: t

(** Escaping of a type variable error. *)
val escaping_typ_var: t

(** Incomplete implementation error. *)
val not_implemented: t

(** Gets the list of errors (error_id, error_msg) *)
val list_errors: unit -> (int * string) list

(** [ERROR(cat, startpos, endpos, msg)]
    describes an error, beginning at position [startpos], ending at
    position [endpos], containing the message [msg]. *)
exception ERROR of t * Lexing.position * Lexing.position * string

val raise_error: t -> Lexing.position -> Lexing.position -> string -> 'a

(** handles the possibly thrown ERROR, prints a message on the error
    channel and exits with a number corresponding with the category of the
    error. *)
val handle_error_and_exit: (unit -> 'a) -> 'a
