open EcPrimeField
   
type group = Z.t

let p = ref Z.zero 

let g = ref Z.zero
              
let cgmul : group -> group -> group = fun a b -> mul_mod a b !p
let cgdiv : group -> group -> group = fun a b -> div_mod a b !p
let cgexp : group -> t -> group = fun a e -> exp_mod a e !p
