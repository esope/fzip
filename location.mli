(** Locations. *)

(** A generic container adding locations to a type. *)
type 'a located =
    { content : 'a ;
      startpos : Lexing.position ;
      endpos : Lexing.position   }

(** Helper function. *)
val locate: 'a -> Lexing.position -> Lexing.position -> 'a located

(** Locating with dummy positions. *)
val dummy_locate: 'a -> 'a located
