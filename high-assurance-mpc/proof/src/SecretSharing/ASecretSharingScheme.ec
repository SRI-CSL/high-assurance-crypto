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
  type rand_t.
  op valid_rand : rand_t -> bool.
  
  op share : rand_t -> secret_t -> (pid_t * share_t) list.
  op public_encoding : secret_t -> (pid_t * share_t) list.
  op reconstruct : (pid_t * share_t) list -> secret_t option.

  axiom correct (r : rand_t) (s : secret_t) :
    valid_rand r =>
    valid_secret s => reconstruct (share r s) = Some s.
  axiom public_encoding_correct x :
    valid_secret x => 
    reconstruct (public_encoding x) = Some x.
  axiom public_encoding_inj x y :
    public_encoding x = public_encoding y =>
    x = y.

  op get_party_share : pid_t -> (pid_t * share_t) list -> share_t.

end SecretSharingScheme.
