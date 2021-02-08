open Utils
open FieldPolynomial
open ECList
open Option

open ASecretSharingScheme

module ShamirData = struct

  let t = Z.of_string "2"

  type secret_t = Z.t
  let valid_secret (x : secret_t) : bool = true

  type share_t = Z.t
  type rand_t = monomial list
  (*let valid_rand (r : rand_t) : bool = *)

  let public_encoding (x : secret_t) : share_t * share_t * share_t * share_t * share_t = (x,x,x,x,x)

  let share (r : rand_t) (x : secret_t) : share_t * share_t * share_t * share_t * share_t = 
    let r = update r Z.zero x in
    (eval !p1 r, eval !p2 r, eval !p3 r, eval !p4 r, eval !p5 r)

  let reconstruct (xx : share_t * share_t * share_t * share_t * share_t) : secret_t option =
    let (x1,x2,x3,x4,x5) = xx in
    Some (interpolate Z.zero (Cons ((!p1, x1), Cons ((!p2, x2), Cons ((!p3, x3), Cons ((!p4, x4), Cons ((!p5, x5), Nil)))))))

end

module Shamir = SecretSharingScheme (ShamirData)
