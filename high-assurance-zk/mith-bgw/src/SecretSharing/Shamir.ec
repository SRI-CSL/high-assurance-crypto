require import Int List.

from General require import ListExt PrimeField FieldPolynomial.
from SecretSharing require import ASecretSharingScheme SecretSharingSchemeSecurity.

theory Shamir.

  const n : {int | 2 <= n} as n_pos.
  const t : {int | 0 <= t < n} as t_pos.

  type pid_t = t.
  op pid_set : pid_t list.
  axiom pid_set_uniq : uniq pid_set.
  axiom pid_set_size : size pid_set = n.
  axiom pid_set_neq0 : forall pid, pid \in pid_set => pid <> fzero.

  type secret_t = t.

  op valid_secret (x : secret_t) : bool = true.

  type share_t = t.
  type shares_t = (pid_t * share_t) list.

  type rand_t = polynomial.
  op valid_rand (r : rand_t) (s : secret_t) : bool =
    degree r = t /\ size r = t+1 /\
    (forall i, 0 <= i < t+1 => (nth mzero r i).`expo = t - i).

  op public_encoding (x : secret_t) : (pid_t * share_t) list = map (fun pid => (pid, x)) pid_set.
  op pub_reconstruct (pid : pid_t) (sh : share_t) : secret_t = sh.

  op share (r : rand_t) (x : secret_t) : (pid_t * share_t) list = 
    let r = update r 0 x in map (fun pid => (pid, eval pid r)) pid_set.

  op reconstruct (xx : (pid_t * share_t) list) : secret_t = (interpolate fzero xx).

  op get_party_share (pid : pid_t) (xs : shares_t) : share_t = oget (assoc xs pid).

  op reconstruct_rand (ss : shares_t) : rand_t = interpolate_poly ss.
  op consistent_shares (i j : pid_t) (shi shj : share_t) : bool = 
    exists r s, valid_rand r s /\ 
                let ss = share r s in 
                get_party_share i ss = shi /\
                get_party_share j ss = shj.

  clone import SecretSharingScheme with
    op n = n,
    op t = t,
    type pid_t = pid_t,
    op pid_set = pid_set,
    type secret_t = secret_t,
    op valid_secret = valid_secret,
    type share_t = share_t,
    type rand_t = rand_t,
    op valid_rand = valid_rand,
    op public_encoding = public_encoding,
    op pub_reconstruct = pub_reconstruct,
    op share = share,
    op reconstruct = reconstruct,
    op get_party_share = get_party_share,
    op consistent_shares = consistent_shares,
    op reconstruct_rand = reconstruct_rand
  proof n_pos, t_pos, pid_set_size, pid_set_uniq, correct, public_encoding_correct,
        public_encoding_inj, unzip1_share, unzip1_public_encoding, public_encoding_reconstruct.
  realize n_pos by smt(n_pos).
  realize t_pos by apply t_pos.
  realize pid_set_size by apply pid_set_size.
  realize pid_set_uniq by apply pid_set_uniq.
  realize correct.
    rewrite /valid_rand /non_zeros_polynomial /valid_secret /share /reconstruct /update => /> 
      r s hdegree hsize hexpo.
    rewrite (interpolate_eval Shamir.pid_set (update r 0 s) fzero) /=; first by apply pid_set_uniq.
      by rewrite degree_update0 hdegree pid_set_size smt(t_pos).
    by rewrite eval_update0; smt(@FieldPolynomial).
  qed.
  realize public_encoding_correct.
    rewrite /reconstruct /public_encoding => /> c.
    by rewrite (interpolate_constant Shamir.pid_set c fzero); first by apply pid_set_uniq.
  qed.
  realize public_encoding_inj. 
    rewrite /public_encoding => x y.
    case (Top.Shamir.pid_set = []); first by smt(pid_set_size n_pos).
    by elim Top.Shamir.pid_set. 
  qed.
  realize unzip1_share.
    by rewrite /share /= => *; rewrite -map_comp /(\o) /= map_id.
  qed.
  realize unzip1_public_encoding.
    by rewrite /public_encoding /= => *; rewrite -map_comp /(\o) /= map_id.
  qed.
  realize public_encoding_reconstruct.
    by move => *; rewrite /public_encoding /= map_assoc //=.
  qed.

  clone import SecretSharingSchemeSecurity with theory SS = SecretSharingScheme.

end Shamir.
