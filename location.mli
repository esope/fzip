type 'a located =
    { content : 'a ;
      startpos : Lexing.position ;
      endpos : Lexing.position   }

val locate: 'a -> Lexing.position -> Lexing.position -> 'a located

val dummy_locate: 'a -> 'a located
