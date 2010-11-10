(** Useful functions related to parsing. *)

open Ast

module String : sig
  module Raw : sig
    open Raw
    module Typ:  sig val parse: string -> typ                  end
    module Kind: sig val parse: string -> typ kind             end
    module Term: sig val parse: string -> (typ kind, typ) term end
  end

  module Typ:  sig val parse: string -> Typ.t  end
  module Kind: sig val parse: string -> Kind.t end
  module Term: sig val parse: string -> Term.t end

end

module Channel : sig
  module Raw : sig
    open Raw
    module Typ:  sig val parse: in_channel -> string -> typ                  end
    module Kind: sig val parse: in_channel -> string -> typ kind             end
    module Term: sig val parse: in_channel -> string -> (typ kind, typ) term end
  end

  module Typ:  sig val parse: in_channel -> string -> Typ.t  end
  module Kind: sig val parse: in_channel -> string -> Kind.t end 
  module Term: sig val parse: in_channel -> string -> Term.t end 

end
