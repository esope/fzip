(** Locations. *)

(** A generic container adding locations to a type. *)
type 'a located =
    { content : 'a ;
      startpos : Lexing.position ;
      endpos : Lexing.position   }

(** Helper functions. *)
val locate: 'a -> Lexing.position -> Lexing.position -> 'a located
val locate_with: 'a -> 'b located -> 'a located
val relocate: 'a located -> Lexing.position -> Lexing.position -> 'a located
val relocate_with: 'a located -> 'b located -> 'a located

val map: ('a -> 'b) -> 'a located -> 'b located

(** Locating with dummy positions. *)
val dummy_locate: 'a -> 'a located
