type 'a option =
  | None
  | Some of 'a

let witness = (Obj.magic None)          

let rec odflt : 'a . 'a -> ('a option) -> 'a =
  fun d2 ox -> begin match ox with
               | None -> d2
               | Some x1 -> x1
               end

let oget (ox: 'a option) : 'a = odflt (Obj.magic None) ox

let rec omap : 'a 'b . ('a -> 'b) -> ('a option) -> ('b option) =
  fun f ox -> begin match ox with
              | None -> None
              | Some x1 -> Some (f x1)
              end
