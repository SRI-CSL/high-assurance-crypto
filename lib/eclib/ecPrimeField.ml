let add_mod a b m = Z.erem (Z.add a b) m

let umin_mod a m = Z.erem (Z.neg a) m
                  
let sub_mod a b m = Z.erem (Z.sub a b) m
                  
let mul_mod a b m = Z.erem (Z.mul a b) m

let div_mod a b m = mul_mod a (Z.invert b m) m
                  
let umin_mod a m = Z.add (Z.neg a) m

let exp_mod a e m = Z.powm a e m

type t = Z.t

let q = ref Z.zero 

let zero : t = Z.zero
let one : t = Z.one

let fadd : t -> t -> t = fun a b -> add_mod a b !q
let fumin : t -> t = fun a -> umin_mod a !q
let fsub : t -> t -> t = fun a b -> sub_mod a b !q
let fmul : t -> t -> t = fun a b -> mul_mod a b !q
let fdiv : t -> t -> t = fun a b -> div_mod a b !q
let fexp : t -> t -> t = fun a e -> exp_mod a e !q

let dt : unit -> Z.t = fun _ -> Z.rem (Z.of_bits (Cryptokit.Random.string Cryptokit.Random.secure_rng 128)) !q
