let add_mod a b m = Z.erem (Z.add a b) m

let umin_mod a m = Z.erem (Z.neg a) m
                  
let sub_mod a b m = Z.erem (Z.sub a b) m
                  
let mul_mod a b m = Z.erem (Z.mul a b) m

let div_mod a b m = mul_mod a (Z.invert b m) m
                  
let umin_mod a m = Z.add (Z.neg a) m

let exp_mod a e m = Z.powm a e m
