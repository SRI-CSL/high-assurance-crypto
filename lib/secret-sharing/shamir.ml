open FieldPolynomial
open EcList
open EcOption
open EcPrimeField

open ASecretSharing

module type PartyConfiguration = sig
  val n : Z.t
  val t : Z.t

  type pid_t = Z.t
  val pid_set : pid_t list
end
   
module ShamirData (PC : PartyConfiguration) = struct

  let n : Z.t = PC.n
  let t : Z.t = PC.n
    
  type pid_t = PC.pid_t
  let pid_set : pid_t list = PC.pid_set

  type secret_t = t

  let valid_secret (x : secret_t) : bool = true

  type share_t = t
  type shares_t = (pid_t * share_t) list

  type rand_t = monomial list

  let public_encoding (x : secret_t) : (pid_t * share_t) list = map (fun pid -> (pid, x)) pid_set
  let pub_reconstruct (pid : pid_t) (sh : share_t) : secret_t = sh

  let share (r : rand_t) (x : secret_t) : (pid_t * share_t) list = 
    let r = update r Z.zero x in map (fun pid -> (pid, eval pid r)) pid_set

  let reconstruct (xx : (pid_t * share_t) list) : secret_t = (interpolate zero xx)

  let get_party_share (pid : pid_t) (xs : shares_t) : share_t = oget (assoc xs pid)

end

module Shamir (PC : PartyConfiguration) = SecretSharingScheme (ShamirData (PC))