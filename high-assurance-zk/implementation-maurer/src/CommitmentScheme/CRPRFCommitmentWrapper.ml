open ECOption
open ECList
open Utils

open NextMsgECCore
open NextMsgArray
open NextMsgMaurerP
open NextMsgMaurerCompat

open ACommitmentScheme
open CRPRF

(* pid, key addr, nins, nrands, msgs *)
external commitment_prover : int -> int -> int -> int -> int -> unit = "commitment_prover_c"
(* pid, key addr, nins, nrands, msgs *)
external commitment_verifier : int -> int -> int -> int -> unit -> bool = "commitment_verifier_c"

module CRPRFCommitmentData = struct
  type msg_t = MaurerProtocol.view_t

  type rand_t = Z.t * int (* pid_ t * ptr_t *)

  type commitment_t = unit
  type opening_string_t = Z.t * int (* pid_ t * ptr_t *)


  let commit (r : rand_t) (m : msg_t) : commitment_t * opening_string_t = 
    let (x, (rs, ims)) = m in
    let nrands = Z.to_int (size rs) in
    let nins = Z.to_int (size (fst x)) + Z.to_int (size (snd x)) in
    let ms = MaurerP.get (snd ims) (Z.of_int 0) in
    let last_m = Aux.either (fun x -> 0) (fun x -> x) (Array.get ms (Z.of_int nrands)) in
      (commitment_prover (Z.to_int (fst r)) (snd r) nins nrands last_m,r)


  let verify (m : msg_t) (ci : commitment_t * opening_string_t) : bool = 
    let (x, (rs, ims)) = m in
    let nrands = Z.to_int (size rs) in
    let nins = Z.to_int (size (fst x)) + Z.to_int (size (snd x)) in
    let (c,r) = ci in 
       commitment_verifier (Z.to_int (fst r)) (snd r) nins nrands c

end

module CRPRFCommitmentWrapper = CommitmentScheme (CRPRFCommitmentData)

