require import Int IntDiv List.

from General require import ListExt.

theory SecretSharingScheme.
  
  const n : {int | 2 <= n} as n_pos.
  const t : {int | 0 <= t < n } as t_pos.

  type pid_t.
  op pid_set : pid_t list.
  axiom pid_set_size : size pid_set = n.
  axiom pid_set_uniq : uniq pid_set.

  type secret_t.
  op valid_secret : secret_t -> bool.

  type share_t.
  type shares_t = (pid_t * share_t) list.
  type rand_t.
  op valid_rand : rand_t -> bool.
  
  op share : rand_t -> secret_t -> (pid_t * share_t) list.
  op public_encoding : secret_t -> (pid_t * share_t) list.
  op pub_reconstruct : pid_t -> share_t -> secret_t.
  (*op reconstruct : (pid_t * share_t) list -> secret_t option.*)
  op reconstruct : (pid_t * share_t) list -> secret_t.

  axiom correct (r : rand_t) (s : secret_t) :
    valid_rand r =>
    valid_secret s => reconstruct (share r s) = s.
  axiom size_share (r : rand_t) (s : secret_t) :
    size (share r s) = n.
  axiom unzip1_share (r : rand_t) (s : secret_t) :
    unzip1 (share r s) = pid_set.
  axiom public_encoding_correct x :
    reconstruct (public_encoding x) = x.
  axiom size_public_encoding (s : secret_t) :
    size (public_encoding s) = n.
  axiom unzip1_public_encoding (s : secret_t) :
    unzip1 (public_encoding s) = pid_set.
  axiom public_encoding_inj x y : public_encoding x = public_encoding y => x = y.
  axiom public_encoding_reconstruct (s : secret_t) :
    forall pid, pid \in pid_set => pub_reconstruct pid (oget (assoc (public_encoding s) pid)) = s.
  axiom public_encoding_rand x :
    valid_secret x => (exists r, valid_rand r /\ share r x = public_encoding x).

  op get_party_share : pid_t -> (pid_t * share_t) list -> share_t.

end SecretSharingScheme.

(*theory ListSecretSharingScheme.

  clone import SecretSharingScheme.
  
  const n = n.
  const t = t.

  type pid_t = pid_t.
  op pid_set : pid_t list = pid_set.

  type secret_t = secret_t list.
  op valid_secret (ss : secret_t) : bool =
    all (fun s => valid_secret s) ss.

  type share_t = (pid_t * share_t) list.
  type rand_t = rand_t list.
  op valid_rand (rs : rand_t) : bool =
    all (fun r => valid_rand r) rs.
  
  op share (rs : rand_t) (ss : secret_t) : share_t list =
    map (fun r_s => let (r,s) = r_s in share r s) (zip rs ss).
  op public_encoding (ss : secret_t) : share_t list =
    map (fun s => public_encoding s) ss.
  op pub_reconstruct : pid_t -> share_t -> secret_t.
  op reconstruct (shs : share_t list) : secret_t option =
    let ors = map (fun sh => reconstruct sh) shs in
    if all (fun or => or <> None) ors then
      Some (map oget ors)
    else None.

  axiom correct (r : rand_t) (s : secret_t) :
    valid_rand r =>
    valid_secret s => reconstruct (share r s) = Some s.
  axiom size_share (r : rand_t) (s : secret_t) :
    size (share r s) = n.
  (*axiom unzip1_share (r : rand_t) (s : secret_t) :
    unzip1 (share r s) = pid_set.*)
  axiom public_encoding_correct x :
    valid_secret x => 
    reconstruct (public_encoding x) = Some x.
  axiom size_public_encoding (s : secret_t) :
    size (public_encoding s) = n.
  (*axiom unzip1_public_encoding (s : secret_t) :
    unzip1 (public_encoding s) = pid_set.*)
  axiom public_encoding_inj x y :
    public_encoding x = public_encoding y =>
    x = y.
  (*axiom public_encoding_reconstruct (s : secret_t) :
    forall pid, pid \in pid_set => pub_reconstruct pid (oget (assoc (public_encoding s) pid)) = s.*)
  axiom public_encoding_rand x :
    valid_secret x => 
    (exists r, valid_rand r /\ share r x = public_encoding x).

  op get_party_share (pid : pid_t) (shs : share_t list) : SecretSharingScheme.share_t list =
    map (fun sh => oget (assoc sh pid)) shs.

end ListSecretSharingScheme.
*)
