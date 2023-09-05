module Pervasive = struct
    type unit = Unit.t
    let tt : unit = ()
    type bool = Bool.t
    let _false : bool = false
    let _true : bool = true
    let not : (bool -> bool) = Bool.not
    let ora : (bool -> (bool -> bool)) = fun x y -> x || y
    let _or : (bool -> (bool -> bool)) = fun x y -> x || y
    let anda : (bool -> (bool -> bool)) = fun x y -> x && y
    let _and : (bool -> (bool -> bool)) = fun x y -> x && y
    let implies : (bool -> (bool -> bool)) = fun x y -> if x then y else true
    let equiv : (bool -> (bool -> bool)) = (fun x y -> x = y)
    let eq : ('a -> ('a -> bool)) = (fun x y -> x = y)
    type int = Z.t
    let witness : 'a = (Obj.magic tt)
    let mk_int : Int.t -> int = Z.of_int
end

let pred1 (c: 'a) (x1: 'a) : Pervasive.bool = x1 = c