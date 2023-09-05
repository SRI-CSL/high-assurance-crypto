open NextMsgECPervasive

module Logic = struct

type 'a option =
  | None
  | Some of 'a
  
  let oget (o:'a option) : 'a =
      match o with
      | None -> Pervasive.witness
      | Some a -> a
  let is_none (o:'a option) : bool = 
      match o with
      | None -> true
      | Some a -> false
  let omap : ('a -> 'b) -> ('a option) -> ('b option) =
        fun f ox -> begin match ox with
                    | None -> None
                    | Some x1 -> Some (f x1)
                    end
  let oapp (f:'a->'b) (b:'b) (o:'a option) : 'b = 
      match o with
      | None -> b
      | Some a -> f a
  let transpose (f : 'a -> 'b -> 'c) (y : 'b) : 'a -> 'c = (fun (x : 'a) -> f x y)
  let idfun (x:'a) : 'a = x
end