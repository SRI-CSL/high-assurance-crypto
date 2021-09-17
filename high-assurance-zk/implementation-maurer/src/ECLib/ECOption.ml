

type 'a option =
  | ECNone
  | ECSome of 'a
      

let odflt : 'a . 'a -> ('a option) -> 'a =
  fun d2 ox -> begin match ox with
               | ECNone -> d2
               | ECSome x1 -> x1
               end

let oget (ox: 'a option) : 'a = odflt (Obj.magic None) ox

let omap : 'a 'b . ('a -> 'b) -> ('a option) -> ('b option) =
  fun f ox -> begin match ox with
              | ECNone -> ECNone
              | ECSome x1 -> ECSome (f x1)
              end
            
let oapp : 'a 'b . ('a -> 'b) -> 'b -> ('a option) -> 'b =
  fun f d ox -> begin match ox with
                | ECNone -> d
                | ECSome x -> f x
                end


