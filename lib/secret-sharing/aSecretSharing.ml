open EcList
open EcOption

module type SecretSharingSchemeData = sig

  val n : Z.t
  val t : Z.t

  type pid_t
  val pid_set : pid_t list

  type secret_t
  val valid_secret : secret_t -> bool

  type share_t
  type shares_t = (pid_t * share_t) list
  type rand_t
  
  val share : rand_t -> secret_t -> (pid_t * share_t) list
  val public_encoding : secret_t -> (pid_t * share_t) list
  val pub_reconstruct : pid_t -> share_t -> secret_t
  val reconstruct : (pid_t * share_t) list -> secret_t

end

module SecretSharingScheme (SSD : SecretSharingSchemeData) = struct

  let n : Z.t = SSD.n
  let t : Z.t = SSD.t

  type pid_t = SSD.pid_t
  let pid_set : pid_t list = SSD.pid_set

  type secret_t = SSD.secret_t
  let valid_secret = SSD.valid_secret

  type share_t = SSD.share_t
  type shares_t = SSD.shares_t
  type rand_t = SSD.rand_t
  
  let share = SSD.share
  let public_encoding = SSD.public_encoding
  let pub_reconstruct = SSD.pub_reconstruct
  let reconstruct = SSD.reconstruct

  let get_party_share (pid : pid_t) (ss : shares_t) : share_t = oget (assoc ss pid)

end

module ListSecretSharing (SSD : SecretSharingSchemeData) = struct
  
  module SS = SecretSharingScheme(SSD)

  let n : Z.t = SS.n
  let t : Z.t = SS.t

  type pid_t = SS.pid_t
  let pid_set : pid_t list = SS.pid_set

  type secret_t = SS.secret_t list
  let valid_secret (ss : secret_t) : bool = 
    all SS.valid_secret ss

  type share_t = SS.share_t list
  type shares_t = (pid_t * share_t) list

  let get_party_share (pid : pid_t) (ss : shares_t) : share_t = oget (assoc ss pid)

  type rand_t = SS.rand_t list

  let share (r : rand_t) (s : secret_t) : shares_t = 
    let ss = map (fun r_s -> let (r,s) = r_s in SS.share r s) (zip r s) in
    map (fun pid -> (pid, map (fun s -> SS.get_party_share pid s) ss)) pid_set
  let public_encoding (s : secret_t) : shares_t =
    let ss = map SS.public_encoding s in
    map (fun pid -> (pid, map (fun s -> SS.get_party_share pid s) ss)) pid_set
  let pub_reconstruct (pid : pid_t) (sh : share_t) : secret_t = witness
  let reconstruct (ss : (pid_t * share_t) list) : secret_t = witness

end
