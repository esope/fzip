include MyString

module Set = Set.Make(MyString)
module Map = Map.Make(MyString)
module AList = struct
  type key = t
  type 'a t = (MyString.t * 'a) list
  let empty = []
  let singleton k v = [(k,v)]
  let add k x l = (k, x) :: l
  let find = List.assoc
  let mem = List.mem_assoc
  let map f = List.map (fun (lab, x) -> (lab, f x))
  let mapi f = List.map (fun (lab, x) -> f lab x)
  let fold f l acc = List.fold_left (fun acc (k,x) -> f k x acc) acc l
  let equal eq l1 l2 =
    try
      List.for_all2 (fun (k1, x1) (k2, x2) -> equal k1 k2 && eq x1 x2) l1 l2
    with Invalid_argument _ -> false
end
