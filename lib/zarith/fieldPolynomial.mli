open EcList
open EcPrimeField
open EcOption

type monomial = {
    coef: t;
    expo: Z.t;
  }

val mzero : monomial

val meval : Z.t -> monomial -> Z.t

val eval : Z.t -> monomial list -> Z.t

val madd : monomial -> monomial -> monomial

val add : monomial list -> monomial list -> monomial list

val mpadd : monomial -> monomial list -> monomial list

val mmul : monomial -> monomial -> monomial

val mpmul : monomial -> monomial list -> monomial list

val mone  : monomial

val one  : monomial list

val mul : monomial list -> monomial list -> monomial list

val mumin : monomial -> monomial

val umin : monomial list -> monomial list

val basis : Z.t -> Z.t list -> monomial list

val interpolate_poly : (Z.t * Z.t) list -> monomial list

val basis : Z.t -> Z.t -> Z.t list -> Z.t

val interpolate : Z.t -> (Z.t * Z.t) list -> Z.t

val update : monomial list -> Z.t -> Z.t -> monomial list
    
val dpolynomial : Z.t -> monomial list

val monomial_to_string : monomial -> string

val polynomial_to_string : monomial list -> string