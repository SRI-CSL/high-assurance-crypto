open NextMsgECPervasive

module Int = struct
    let min : Pervasive.int -> Pervasive.int -> Pervasive.int = Z.min
    let le : Pervasive.int -> Pervasive.int -> Pervasive.bool = Z.leq
    let lt : Pervasive.int -> Pervasive.int -> Pervasive.bool = Z.lt
    let plus : Pervasive.int -> Pervasive.int -> Pervasive.int = Z.add
    let minus : Pervasive.int -> Pervasive.int -> Pervasive.int = Z.sub
end