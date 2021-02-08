open ECList
open Option
   
open Utils

module type SecretSharingSchemeData = sig

  val t : Z.t
  
  type secret_t
  val valid_secret : secret_t -> bool

  type share_t
  type rand_t
  (*val valid_rand : rand_t -> bool*)

  val share : rand_t -> secret_t -> (share_t * share_t * share_t * share_t * share_t)
  val public_encoding : secret_t -> (share_t * share_t * share_t * share_t * share_t)
  val reconstruct : (share_t * share_t * share_t * share_t * share_t) -> secret_t option

end

module SecretSharingScheme (SSD : SecretSharingSchemeData) = struct

  let t = SSD.t

  type pid_t = pid_mpc_t

  type secret_t = SSD.secret_t
  let valid_secret = SSD.valid_secret

  type share_t = SSD.share_t
  type shares_t = share_t * share_t * share_t * share_t * share_t
  let get_party_share (pid : pid_t) (ss : shares_t) : share_t =
    match pid with
      | P1 -> let (s1,s2,s3,s4,s5) = ss in s1
      | P2 -> let (s1,s2,s3,s4,s5) = ss in s2
      | P3 -> let (s1,s2,s3,s4,s5) = ss in s3
      | P4 -> let (s1,s2,s3,s4,s5) = ss in s4
      | P5 -> let (s1,s2,s3,s4,s5) = ss in s5

  type rand_t = SSD.rand_t
  (*let valid_rand = SSD.valid_rand*)

  let share = SSD.share
  let public_encoding = SSD.public_encoding
  let reconstruct = SSD.reconstruct

end

module ListSecretSharing (SSD : SecretSharingSchemeData) = struct
  
  module SS = SecretSharingScheme(SSD)
  open SS

  type secret_t = SS.secret_t list
  let valid_secret (ss : secret_t) : bool = 
    all SS.valid_secret ss

  type share_t = SS.share_t list
  type shares_t = SS.shares_t list

  let get_party_share (pid : pid_t) (ss : shares_t) : share_t =
    map (SS.get_party_share pid) ss

  type rand_t = SS.rand_t list
  (*let valid_rand (rr : rand_t) (ss : secret_t) : bool = 
    size rr = size ss &&
    all (fun r -> valid_rand r) rr*)

  let share (r : rand_t) (s : secret_t) : shares_t = 
    map (fun r_s -> let (r,s) = r_s in SS.share r s) (zip r s)
  let public_encoding (s : secret_t) : shares_t = map SS.public_encoding s
  let reconstruct (ss : shares_t) : secret_t option = 
    let sos = map SS.reconstruct ss in
    if all (fun s -> s <> None) sos then
      Some (map oget sos)
    else None

end
