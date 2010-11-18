type 'a located =
    { content : 'a ;
      startpos : Lexing.position ;
      endpos : Lexing.position   }

let locate x startpos endpos =
  { content = x ; startpos = startpos ; endpos = endpos }

let locate_with content { startpos ; endpos ; _ } =
  { content ; startpos ; endpos }

let relocate r startpos endpos =
  { r with startpos = startpos ; endpos = endpos }

let relocate_with { content ; _ } { startpos ; endpos ; _ } =
  { content ; startpos ; endpos }

let map f r = locate_with (f r.content) r

let dummy_locate x =
  let dummy = Lexing.dummy_pos in
  locate x dummy dummy

let location_msg { startpos ; endpos ; _ } =
  let open Lexing in
  Printf.sprintf "file \"%s\", line %i, characters %i-%i"
      startpos.pos_fname startpos.pos_lnum startpos.pos_cnum
      (endpos.pos_cnum + (endpos.pos_bol - startpos.pos_bol))
