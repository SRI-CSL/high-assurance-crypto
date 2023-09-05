require import Int IntDiv List Distr DList Real.

from General require import PrimeField ListExt FieldPolynomial.
from ArithmeticProtocol require import SMultiplicationGate.
from Functionalities require import SMultiplicationFunctionality.
from MPC require import GateWeak.
from SecretSharing require import Shamir.

theory BGWSMultiplication.

  clone import Shamir.

  type pinput_t = share_t.
  type sinput_t = share_t.
  type input_t = pinput_t * sinput_t.
  type inputs_t = (pid_t * input_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (input pid xs).
  op valid_inputs (xs : inputs_t) : bool =
    unzip1 xs = pid_set /\
    let pub = map (fun pid => (pid, pinput pid xs)) pid_set in
    let sec = map (fun pid => (pid, sinput pid xs)) pid_set in
    (exists s, valid_secret s /\ pub = public_encoding s) /\
    (exists r s', valid_secret s' /\ valid_rand r s' /\ share r s' = sec).

  type rand_t = unit.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand (r : rand_t) : bool = true.
  op valid_rands (rs : rands_t) : bool =
    unzip1 rs = pid_set /\ (forall pid, pid \in pid_set => valid_rand (rand pid rs)).

  type output_t = secret_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  type msgs_t = unit.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to (pid : pid_t) (ms : out_messages_t) : msgs_t = oget (assoc ms pid).
  op get_messages_from (pid : pid_t) (ms : in_messages_t) : msgs_t = oget (assoc ms pid).

  type trace_t = shares_t * in_messages_t.
  type traces_t = (pid_t * in_messages_t) list.
  op trace (pid : pid_t) (tr : traces_t) : in_messages_t = oget (assoc tr pid).
  
  type view_t = input_t * rand_t * trace_t.

  op party_exec (pid : pid_t) (r : rand_t) (x : input_t) : output_t = 
    let (pub, sec) = x in fmul (pub_reconstruct pid pub) sec.
  op empty_trace : in_messages_t = [].

  op out_messages_in_messages (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : out_messages_t = [].

  op local_output_share (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : share_t =
    let (pub, sec) = x in party_exec pid r x.

  op eval (rs : rands_t) (xs : inputs_t) : (pid_t * ((pid_t * msgs_t) list)) list * shares_t =
    let tr = map (fun pid => (pid, [])) pid_set in
    let ys = map (fun pid => (pid, party_exec pid (oget (assoc rs pid)) 
                                              (oget (assoc xs pid)))) pid_set in
    (tr,ys).

  clone import SMultiplicationGate with
    op SMultiplicationFunctionality.SecretSharingScheme.n = Shamir.SecretSharingScheme.n,
    op SMultiplicationFunctionality.SecretSharingScheme.t = Shamir.SecretSharingScheme.t,
    type SMultiplicationFunctionality.SecretSharingScheme.pid_t = Shamir.SecretSharingScheme.pid_t,
    op SMultiplicationFunctionality.SecretSharingScheme.pid_set = Shamir.SecretSharingScheme.pid_set,
    op SMultiplicationFunctionality.SecretSharingScheme.valid_secret = Shamir.SecretSharingScheme.valid_secret,
    type SMultiplicationFunctionality.SecretSharingScheme.share_t = Shamir.SecretSharingScheme.share_t,
    type SMultiplicationFunctionality.SecretSharingScheme.rand_t = Shamir.SecretSharingScheme.rand_t,
    op SMultiplicationFunctionality.SecretSharingScheme.valid_rand = Shamir.SecretSharingScheme.valid_rand,
    op SMultiplicationFunctionality.SecretSharingScheme.share = Shamir.SecretSharingScheme.share,
    op SMultiplicationFunctionality.SecretSharingScheme.public_encoding = Shamir.SecretSharingScheme.public_encoding,
    op SMultiplicationFunctionality.SecretSharingScheme.pub_reconstruct = Shamir.SecretSharingScheme.pub_reconstruct,
    op SMultiplicationFunctionality.SecretSharingScheme.reconstruct = Shamir.SecretSharingScheme.reconstruct,
    op SMultiplicationFunctionality.SecretSharingScheme.get_party_share = Shamir.SecretSharingScheme.get_party_share,

    type rand_t = rand_t,
    op valid_rand = valid_rand,
    type msgs_t = msgs_t,
    op get_messages_to = get_messages_to,
    op get_messages_from = get_messages_from,
    op out_messages_in_messages = out_messages_in_messages,
    op local_output_share = local_output_share,
    op eval = eval
  proof SMultiplicationFunctionality.GateFunctionality.n_pos, 
        SMultiplicationFunctionality.GateFunctionality.t_pos,
        SMultiplicationFunctionality.GateFunctionality.pid_set_size,
        SMultiplicationFunctionality.GateFunctionality.pid_set_uniq,
        Gate.GateFunctionality.n_pos,
        Gate.GateFunctionality.t_pos,
        SMultiplicationFunctionality.SecretSharingScheme.n_pos,
        SMultiplicationFunctionality.SecretSharingScheme.t_pos,
        SMultiplicationFunctionality.SecretSharingScheme.pid_set_size,
        SMultiplicationFunctionality.SecretSharingScheme.pid_set_uniq,
        SMultiplicationFunctionality.SecretSharingScheme.correct,
        SMultiplicationFunctionality.SecretSharingScheme.size_share,
        SMultiplicationFunctionality.SecretSharingScheme.unzip1_share,
        SMultiplicationFunctionality.SecretSharingScheme.public_encoding_correct,
        SMultiplicationFunctionality.SecretSharingScheme.size_public_encoding,
        SMultiplicationFunctionality.SecretSharingScheme.unzip1_public_encoding,
        SMultiplicationFunctionality.SecretSharingScheme.public_encoding_inj,
        SMultiplicationFunctionality.SecretSharingScheme.public_encoding_reconstruct,
        SMultiplicationFunctionality.SecretSharingScheme.public_encoding_rand,
        eval_domain, local_output_share_correct, out_messages_in_messages_consistency,
        eval_preserves_share, Gate.correct, Gate.correct_domain.
  realize SMultiplicationFunctionality.GateFunctionality.n_pos by apply n_pos.
  realize SMultiplicationFunctionality.GateFunctionality.t_pos by apply t_pos.
  realize SMultiplicationFunctionality.GateFunctionality.pid_set_size by apply pid_set_size.
  realize SMultiplicationFunctionality.GateFunctionality.pid_set_uniq by apply pid_set_uniq.
  realize Gate.GateFunctionality.n_pos by apply n_pos.
  realize Gate.GateFunctionality.t_pos by apply t_pos.
  realize SMultiplicationFunctionality.SecretSharingScheme.n_pos by apply n_pos.
  realize SMultiplicationFunctionality.SecretSharingScheme.t_pos by apply t_pos.
  realize SMultiplicationFunctionality.SecretSharingScheme.pid_set_size by apply pid_set_size.
  realize SMultiplicationFunctionality.SecretSharingScheme.pid_set_uniq by apply pid_set_uniq.
  realize SMultiplicationFunctionality.SecretSharingScheme.correct by move : Shamir.SecretSharingScheme.correct => /#.
  realize SMultiplicationFunctionality.SecretSharingScheme.size_share by move : Shamir.SecretSharingScheme.size_share => /#.
  realize SMultiplicationFunctionality.SecretSharingScheme.unzip1_share by move : Shamir.SecretSharingScheme.unzip1_share => /#.
  realize SMultiplicationFunctionality.SecretSharingScheme.public_encoding_correct by move : Shamir.SecretSharingScheme.public_encoding_correct => /#.
  realize SMultiplicationFunctionality.SecretSharingScheme.size_public_encoding by move : Shamir.SecretSharingScheme.size_public_encoding => /#.
  realize SMultiplicationFunctionality.SecretSharingScheme.unzip1_public_encoding by move : Shamir.SecretSharingScheme.unzip1_public_encoding => /#.
  realize SMultiplicationFunctionality.SecretSharingScheme.public_encoding_inj by move : Shamir.SecretSharingScheme.public_encoding_inj => /#.
  realize SMultiplicationFunctionality.SecretSharingScheme.public_encoding_reconstruct by move : Shamir.SecretSharingScheme.public_encoding_reconstruct => /#.
  realize SMultiplicationFunctionality.SecretSharingScheme.public_encoding_rand by move : Shamir.SecretSharingScheme.public_encoding_rand => /#.
  realize eval_domain.
rewrite /eval /=; progress.
by rewrite -map_comp /(\o) /= map_id //=.
  qed.
  realize local_output_share_correct.
rewrite /eval /= /party_exec /=.
progress.
rewrite !map_assoc //=.
rewrite /party_exec /=.
rewrite /local_output_share /= /input /=.
rewrite /party_exec  /=.
smt().
  qed.
  realize out_messages_in_messages_consistency.
by rewrite /gate /eval /=.
  qed.  
  realize Gate.correct.
    rewrite /valid_inputs /valid_input /valid_inputs /valid_rands /valid_rand /output_pred
            /input_pred /gate /eval /party_exec /f /sum_pair /reconstruct /o /=.
    move => rs xs => />; progress.
    rewrite /to_foutput /= -H6.
    progress.
        have ->: interpolate fzero ((share r s')) = s'.
          move : (SMultiplicationFunctionality.SecretSharingScheme.correct r s').
          move : H0; rewrite /valid_secret /=.
          by rewrite /valid_rand H3 H4 /= /reconstruct /#. 
      move : H6; rewrite /share /=.
      rewrite -eq_in_map /sinput /input; progress.
    rewrite /pub_reconstruct /= /pinput /input /=.
    have ->: (map (fun (pid0 : pid_t) => (pid0, let (pub, sec) = oget (assoc xs pid0) in fmul pub sec)) pid_set) = (map (fun (pid : pid_t) => (pid, eval pid (smul (oget (assoc xs (head witness Shamir.pid_set))).`1 (update r 0 s')))) pid_set).
      rewrite -eq_in_map /=; progress; rewrite eval_smul.
      by move : H1; rewrite /public_encoding /share /= -!eq_in_map /= /#.
      rewrite /reconstruct.
      * rewrite (interpolate_eval pid_set (smul (oget (assoc xs (head witness Shamir.pid_set))).`1 (update r 0 s'))).
          by apply pid_set_uniq.
          by rewrite degree_smul !degree_update0 H3 pid_set_size /max /=; smt(t_pos).
        rewrite -update_smul; first by rewrite expo_diff_count //; rewrite ?H2 ?H7; smt(t_pos).
        rewrite !eval_update0 => //.
        rewrite expo_diff_count //; first by rewrite size_smul; rewrite ?H2 ?H7; smt(t_pos).
        rewrite size_smul => i hi; rewrite smul_expo; first by done.
        by rewrite H5 /#. 
      rewrite /pinputs /=; rewrite -eq_in_map => x; progress.
      by rewrite !map_assoc //=; first by smt(@List n_pos).
  qed.
  realize Gate.correct_domain.
    by move => rs xs; rewrite /gate /eval /= /party_exec -!map_comp /(\o) /= !map_id /pid_set.
  qed.
  realize eval_preserves_share.
    rewrite /valid_inputs /valid_input /valid_inputs /valid_rands /valid_rand /output_pred
            /input_pred /gate /eval /party_exec /f /sum_pair /reconstruct /o /=.
progress.
exists (smul s (update r 0 s')).
        rewrite /valid_rand degree_smul degree_update0 size_smul size_update0 H3 H4; progress.
          rewrite smul_expo; first by rewrite size_update0 H4 //.
          rewrite update_expo; first by rewrite H4 //.
          by rewrite H5.
        rewrite /share /= -eq_in_map /=; progress.
        rewrite eval_update //. 
          rewrite expo_diff_count //.
            by rewrite size_smul size_update0 H4; smt. 
            rewrite size_smul size_update0 H4; progress.
            rewrite smul_expo; first by rewrite size_update0 H4 //.
            rewrite update_expo; first by rewrite H4 //.
            by rewrite H5 //.
        rewrite get_monomial0.
          rewrite expo_diff_count //; first by rewrite size_smul size_update0 H4; smt. 
          rewrite size_smul size_update0 H4; progress.
          rewrite smul_expo; first by rewrite size_update0 H4 //.
          rewrite update_expo; first by rewrite H4 //.
          by rewrite H5 //.
        rewrite /meval /= !pow0 !mulf1 !eval_smul eval_update0.
          by (rewrite expo_diff_count //; first by smt) => /#. 
        rewrite /pub_reconstruct.
      move : H6; rewrite /share /=.
      rewrite -eq_in_map /sinput /input; progress.
    rewrite /pub_reconstruct /= /pinput /input /=.
    have ->: (map (fun (pid0 : pid_t) => (pid0, let (pub, sec) = oget (assoc xs pid0) in fmul pub sec)) pid_set) = (map (fun (pid : pid_t) => (pid, eval pid (smul (oget (assoc xs x)).`1 (update r 0 s')))) pid_set).
      rewrite -eq_in_map /=; progress; rewrite eval_smul.
      by move : H1; rewrite /public_encoding /share /= -!eq_in_map /= /#.
      rewrite /reconstruct.
      * rewrite (interpolate_eval pid_set (smul (oget (assoc xs x)).`1 (update r 0 s'))).
          by apply pid_set_uniq.
          by rewrite degree_smul !degree_update0 H3 pid_set_size /max /=; smt(t_pos).
        rewrite -update_smul; first by rewrite expo_diff_count //; rewrite ?H2 ?H7; smt(t_pos).
        rewrite !eval_update0 => //.
        rewrite expo_diff_count //; first by rewrite size_smul; rewrite ?H2 ?H7; smt(t_pos).
        rewrite size_smul => i hi; rewrite smul_expo; first by done.
        by rewrite H5 /#. 
have : exists (pub, sec), (pub, sec) = oget (assoc xs x).
exists (oget (assoc xs x)).`1 (oget (assoc xs x)).`2 => /#.
progress.
rewrite  -H9 /=.
rewrite H6 //=.
have ->: (oget (assoc xs x)).`2 = sec by smt().
have ->: pub = s.
move : H1; rewrite /pinput /= /input /=.
rewrite /public_encoding /=.
rewrite -eq_in_map; progress.
smt().
by ringeq.
qed.

  op simulator (rs : rands_t) (xs : inputs_t) (cr : pid_t list) : SMultiplicationGate.Gate.poutputs_t * (pid_t * (SMultiplicationFunctionality.input_t * SMultiplicationGate.Gate.rand_t * SMultiplicationGate.Gate.in_messages_t)) list =
    let ys = map (fun pid => (pid, party_exec pid (rand pid rs) (input pid xs))) cr in
    let vs = (map (fun pid => (pid, (oget (assoc xs pid), (), []))) cr) in (ys, vs).

  clone import WeakSecurity as SMulSec with 
    theory Gate <- SMultiplicationGate.Gate,
    op simulator = simulator.

  section Security.

    declare module D : Distinguisher_t{RealEvaluator,IdealEvaluator}.

    module R : Rand_t = {
      proc gen(aux : aux_t, cr : pid_t list) : rands_t = {
        return (map (fun pid => (pid, ())) pid_set);
      }
    }.

    equiv real_ideal_equiv :
      GameReal(D,R).main ~ GameIdeal(D,R).main :
      ={glob D, glob R, x, aux} ==> ={res}.
    proof.
      proc.
      seq 1 1 : (#pre /\ ={xs,cr}); first by call (_ : true).
      seq 1 1 : (#pre /\ ={r}); first by call (_ : true).
      (if; first by smt()); last by rnd.
      inline *.
      call (_ : true).
      wp; skip; progress.
      move : H H0; rewrite /valid_inputs /valid_rands /valid_rand; progress.
      rewrite /extract_inputs /extract_rands /extract_traces /=.
      rewrite /simulator /= /party_exec /= /input /= /output.

rewrite -eq_in_map => pid; progress.
rewrite /trace !map_assoc //= /gate /= /eval /=.
rewrite !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().

rewrite /simulator /=.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.
rewrite /gate /eval /= /trace !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().
qed.

    lemma security &m aux cr :
      Pr [ GameReal(D,R).main(aux,cr) @ &m : res ] - Pr [ GameIdeal(D,R).main(aux,cr) @ &m : res ] = 0%r.
    proof. 
      progress.
      have ?: Pr [ GameReal(D,R).main(aux,cr) @ &m : res ] = Pr [ GameIdeal(D,R).main(aux,cr) @ &m : res ] by byequiv real_ideal_equiv. 
      by smt().
    qed.
    
  end section Security.

end BGWSMultiplication.
