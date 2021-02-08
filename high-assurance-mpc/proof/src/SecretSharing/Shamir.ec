require import Int List.

from General require import ListExt PrimeField FieldPolynomial.
from SecretSharing require import ASecretSharingScheme SecretSharingSchemeSecurity.

theory Shamir.

print SecretSharingScheme.

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

  type rand_t = polynomial.

  op valid_rand (r : rand_t) : bool =
    degree r = t /\
    size r = t+1 /\
    (forall i, 0 <= i < t+1 => (nth mzero r i).`expo = t - i).

  op public_encoding (x : secret_t) : (pid_t * share_t) list = 
    map (fun pid => (pid, x)) pid_set.

  op share (r : rand_t) (x : secret_t) : (pid_t * share_t) list = 
    let r = update r 0 x in
    map (fun pid => (pid, eval pid r)) pid_set.

  op reconstruct (xx : (pid_t * share_t) list) : secret_t option =
    Some (interpolate fzero xx).

  clone import SecretSharingScheme as Shamir with
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
    op share = share,
    op reconstruct = reconstruct
  proof *.
  realize n_pos by apply n_pos.
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
    rewrite /reconstruct /public_encoding => /> s hvalid.
    by rewrite (interpolate_constant Shamir.pid_set s fzero); first by apply pid_set_uniq.
  qed.
  realize public_encoding_inj. 
    rewrite /public_encoding => x y.
    case (Top.Shamir.pid_set = []); first by smt(pid_set_size n_pos).
    by elim Top.Shamir.pid_set. 
  qed.

  clone import SecretSharingSchemeSecurity with theory SecretSharingScheme <- Shamir.

end Shamir.
