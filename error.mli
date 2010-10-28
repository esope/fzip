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

(** [raise_error cat startpos endpos msg] prints a message on the
    error channel, beginning at position [startpos], ending at
    position [endpos], containing the message [msg]. The program exits
    with error number [cat]. *)
val raise_error: t -> Lexing.position -> Lexing.position -> string -> 'a
