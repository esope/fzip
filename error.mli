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

(** Type wellformedness error. *)
val subtype: t

(** Kind wellformedness error. *)
val subkind: t

(** Zipping of environment error. *)
val zip: t

(** Purity of environment error. *)
val purity: t

(** Incomplete implementation error. *)
val not_implemented: t

(** Gets the list of errors (error_id, error_msg) *)
val list_errors: unit -> (int * string) list

(** [raise_error cat startpos endpos msg] prints a message on the
    error channel, beginning at position [startpos], ending at
    position [endpos], containing the message [msg]. The program exits
    with error number [cat]. *)
val raise_error: t -> Lexing.position -> Lexing.position -> string -> 'a
