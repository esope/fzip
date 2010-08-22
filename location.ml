type 'a located =
    { content : 'a ;
      startpos : Lexing.position ;
      endpos : Lexing.position   }

let locate x startpos endpos =
  { content = x ; startpos = startpos ; endpos = endpos }

let dummy_locate x =
  let dummy = Lexing.dummy_pos in
  locate x dummy dummy
