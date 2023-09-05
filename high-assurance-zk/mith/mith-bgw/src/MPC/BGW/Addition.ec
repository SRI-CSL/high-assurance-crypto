require import Int IntDiv List Distr DList Real.

from General require import PrimeField ListExt FieldPolynomial.
from ArithmeticProtocol require import AdditionGate.
from Functionalities require import AdditionFunctionality.
from MPC require import GateWeak.
from SecretSharing require import Shamir.

theory BGWAddition.

  clone import Shamir.

  type pinput_t = unit.
  type sinput_t = share_t * share_t.
  type input_t = pinput_t * sinput_t.
  type inputs_t = (pid_t * input_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (input pid xs).
  op valid_inputs (xs : inputs_t) : bool = 
    unzip1 xs = pid_set /\
    let sec1 = map (fun pid => (pid, fst (sinput pid xs))) pid_set in
    let sec2 = map (fun pid => (pid, snd (sinput pid xs))) pid_set in
    (exists r s, valid_secret s /\ valid_rand r s /\ share r s = sec1) /\ 
    (exists r' s', valid_secret s' /\ valid_rand r' s' /\ share r' s' = sec2).

  type rand_t = unit.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand (r : rand_t) : bool = true.
  op valid_rands (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ (forall pid, pid \in pid_set => valid_rand (rand pid rs)).

  type output_t = secret_t.
  type outputs_t = (pid_t * share_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  type msgs_t = unit.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to (pid : pid_t) (ms : out_messages_t) : msgs_t = oget (assoc ms pid).
  op get_messages_from (pid : pid_t) (im : in_messages_t) : msgs_t = oget (assoc im pid).

  type trace_t = shares_t * in_messages_t.
  type traces_t = (pid_t * in_messages_t) list.
  op trace (pid : pid_t) (tr : traces_t) : in_messages_t = oget (assoc tr pid).
  
  type view_t = input_t * rand_t * trace_t.

  op party_exec (r : rand_t) (x : input_t) : output_t = 
    let (pub, sec) = x in let (x1,x2) = sec in fadd x1 x2.
  op empty_trace : (pid_t * msgs_t) list = [].

  op out_messages_in_messages (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : out_messages_t = [].

  op local_output_share (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : share_t =
    let (pub, sec) = x in
    let (x1, x2) = sec in fadd x1 x2.

  op eval (rs : rands_t) (xs : inputs_t) : (pid_t * ((pid_t * msgs_t) list)) list * shares_t =
    let tr = map (fun pid => (pid, [])) pid_set in
    let ys = map (fun pid => (pid, party_exec (oget (assoc rs pid)) 
                                              (oget (assoc xs pid)))) pid_set in
    (tr,ys).

  clone import AdditionGate with
    op AdditionFunctionality.SecretSharingScheme.n = Shamir.SecretSharingScheme.n,
    op AdditionFunctionality.SecretSharingScheme.t = Shamir.SecretSharingScheme.t,
    type AdditionFunctionality.SecretSharingScheme.pid_t = Shamir.SecretSharingScheme.pid_t,
    op AdditionFunctionality.SecretSharingScheme.pid_set = Shamir.SecretSharingScheme.pid_set,
    op AdditionFunctionality.SecretSharingScheme.valid_secret = Shamir.SecretSharingScheme.valid_secret,
    type AdditionFunctionality.SecretSharingScheme.share_t = Shamir.SecretSharingScheme.share_t,
    type AdditionFunctionality.SecretSharingScheme.rand_t = Shamir.SecretSharingScheme.rand_t,
    op AdditionFunctionality.SecretSharingScheme.valid_rand = Shamir.SecretSharingScheme.valid_rand,
    op AdditionFunctionality.SecretSharingScheme.share = Shamir.SecretSharingScheme.share,
    op AdditionFunctionality.SecretSharingScheme.public_encoding = Shamir.SecretSharingScheme.public_encoding,
    op AdditionFunctionality.SecretSharingScheme.pub_reconstruct = Shamir.SecretSharingScheme.pub_reconstruct,
    op AdditionFunctionality.SecretSharingScheme.reconstruct = Shamir.SecretSharingScheme.reconstruct,
    op AdditionFunctionality.SecretSharingScheme.get_party_share = Shamir.SecretSharingScheme.get_party_share,

    type rand_t = rand_t,
    op valid_rand = valid_rand,
    type msgs_t = msgs_t,
    op get_messages_to = get_messages_to,
    op get_messages_from = get_messages_from,
    op out_messages_in_messages = out_messages_in_messages,
    op local_output_share = local_output_share,
    op eval = eval
  proof AdditionFunctionality.GateFunctionality.n_pos, 
        AdditionFunctionality.GateFunctionality.t_pos,
        AdditionFunctionality.GateFunctionality.pid_set_size,
        AdditionFunctionality.GateFunctionality.pid_set_uniq,
        Gate.GateFunctionality.n_pos,
        Gate.GateFunctionality.t_pos,
        AdditionFunctionality.SecretSharingScheme.n_pos,
        AdditionFunctionality.SecretSharingScheme.t_pos,
        AdditionFunctionality.SecretSharingScheme.pid_set_size,
        AdditionFunctionality.SecretSharingScheme.pid_set_uniq,
        AdditionFunctionality.SecretSharingScheme.correct,
        AdditionFunctionality.SecretSharingScheme.size_share,
        AdditionFunctionality.SecretSharingScheme.unzip1_share,
        AdditionFunctionality.SecretSharingScheme.public_encoding_correct,
        AdditionFunctionality.SecretSharingScheme.size_public_encoding,
        AdditionFunctionality.SecretSharingScheme.unzip1_public_encoding,
        AdditionFunctionality.SecretSharingScheme.public_encoding_inj,
        AdditionFunctionality.SecretSharingScheme.public_encoding_reconstruct,
        AdditionFunctionality.SecretSharingScheme.public_encoding_rand,
        eval_domain, local_output_share_correct, out_messages_in_messages_consistency,
        eval_preserves_share, Gate.correct, Gate.correct_domain.
  realize AdditionFunctionality.GateFunctionality.n_pos by apply n_pos.
  realize AdditionFunctionality.GateFunctionality.t_pos by apply t_pos.
  realize AdditionFunctionality.GateFunctionality.pid_set_size by apply pid_set_size.
  realize AdditionFunctionality.GateFunctionality.pid_set_uniq by apply pid_set_uniq.
  realize Gate.GateFunctionality.n_pos by apply n_pos.
  realize Gate.GateFunctionality.t_pos by apply t_pos.
  realize AdditionFunctionality.SecretSharingScheme.n_pos by apply n_pos.
  realize AdditionFunctionality.SecretSharingScheme.t_pos by apply t_pos.
  realize AdditionFunctionality.SecretSharingScheme.pid_set_size by apply pid_set_size.
  realize AdditionFunctionality.SecretSharingScheme.pid_set_uniq by apply pid_set_uniq.
  realize AdditionFunctionality.SecretSharingScheme.correct by move : Shamir.SecretSharingScheme.correct => /#.
  realize AdditionFunctionality.SecretSharingScheme.size_share by move : Shamir.SecretSharingScheme.size_share => /#.
  realize AdditionFunctionality.SecretSharingScheme.unzip1_share by move : Shamir.SecretSharingScheme.unzip1_share => /#.
  realize AdditionFunctionality.SecretSharingScheme.public_encoding_correct by move : Shamir.SecretSharingScheme.public_encoding_correct => /#.
  realize AdditionFunctionality.SecretSharingScheme.size_public_encoding by move : Shamir.SecretSharingScheme.size_public_encoding => /#.
  realize AdditionFunctionality.SecretSharingScheme.unzip1_public_encoding by move : Shamir.SecretSharingScheme.unzip1_public_encoding => /#.
  realize AdditionFunctionality.SecretSharingScheme.public_encoding_inj by move : Shamir.SecretSharingScheme.public_encoding_inj => /#.
  realize AdditionFunctionality.SecretSharingScheme.public_encoding_reconstruct by move : Shamir.SecretSharingScheme.public_encoding_reconstruct => /#.
  realize AdditionFunctionality.SecretSharingScheme.public_encoding_rand by move : Shamir.SecretSharingScheme.public_encoding_rand => /#.
  realize eval_domain.
rewrite /eval /=; progress.
by rewrite -map_comp /(\o) /= map_id //=.
  qed.
  realize local_output_share_correct.
rewrite /eval /=.
progress.
by rewrite !map_assoc //=.
  qed.
  realize out_messages_in_messages_consistency.
by rewrite /gate /eval /=.
  qed.  
  realize Gate.correct.
    rewrite /valid_inputs /valid_input /valid_inputs /valid_rands /valid_rand /output_pred
            /input_pred /gate /eval /party_exec /f /sum_pair /reconstruct /o /=.
    move => rs xs => />; progress.
    rewrite /to_foutput /= -H4 -H9.
    progress.
        have ->: interpolate fzero ((share r s)) = s.
          move : (Shamir.SecretSharingScheme.correct r s).
          move : H0; rewrite /valid_secret /=.
          by rewrite /valid_rand H1 H2 /= /reconstruct /#. 
        have ->: interpolate fzero ((share r' s')) = s'.
          move : (Shamir.SecretSharingScheme.correct r' s').
          move : H5; rewrite /valid_secret /=.
          by rewrite /valid_rand H6 H7 /= /reconstruct /#.
        have ->: map (fun (pid : pid_t) => (pid, let (_, sec) = oget (assoc xs pid) in let (x1, x2) = sec in fadd x1 x2)) pid_set = map (fun (pid : pid_t) => (pid, fadd (eval pid (update r 0 s)) (eval pid (update r' 0 s')))) pid_set.
          rewrite -(eq_in_map ((fun (pid : pid_t) => (pid, let (_, sec) = oget (assoc xs pid) in let (x1, x2) = sec in fadd x1 x2))) (fun (pid : pid_t) => (pid, fadd (eval pid (update r 0 s)) (eval pid (update r' 0 s'))))).
          move => x hx /=.
          move : H4 H9.
          by rewrite /share /= -!eq_in_map /sinput /AdditionFunctionality.input /#.
        have ->: (map (fun (pid : pid_t) => (pid, fadd (eval pid (update r 0 s)) (eval pid (update r' 0 s')))) pid_set) = (map (fun (pid : pid_t) => (pid, eval pid (add (update r 0 s) (update r' 0 s')))) pid_set).
          rewrite -eq_in_map => x hx /=.
          by rewrite eval_add.
        rewrite /reconstruct (interpolate_eval pid_set (add (update r 0 s) (update r' 0 s'))).
          by apply pid_set_uniq.
          by rewrite degree_add !degree_update0 H1 H6 pid_set_size /max /=; smt(t_pos).
        rewrite -update_add; first 2 by rewrite expo_diff_count //; rewrite ?H2 ?H7; smt(t_pos).
        rewrite !eval_update0 => //.
          rewrite expo_diff_count //; first by rewrite size_add; rewrite H2 ?H7; smt(t_pos).
          rewrite !size_add; first 2 by rewrite H2 /#.
          move => i hi; rewrite add_expos; first 3 by rewrite H2 /#. 
          by rewrite H3 /#. 
          by rewrite expo_diff_count //; first 2 by rewrite ?H2 ?H7; smt(t_pos).
          by rewrite expo_diff_count //; first 2 by rewrite H7; smt(t_pos).
  qed.
  realize Gate.correct_domain.
    by move => rs xs; rewrite /gate /eval /= /party_exec -!map_comp /(\o) /= !map_id /pid_set.
  qed.
  realize eval_preserves_share.
rewrite /valid_inputs /=.
rewrite /valid_rands /=.
rewrite /valid_secret /valid_rand /=.
progress.
exists (add r r').
rewrite size_add.
smt().
smt().
rewrite degree_add.
rewrite H4 H0 /max /=.
rewrite H1 /=.
have ->: (forall (i : int), 0 <= i && i < t + 1 => (nth mzero (add r r') i).`expo = t - i) <=> true.
progress.
rewrite add_expos.
smt().
smt().
smt().
smt().
simplify.
have ->: x2 = (AdditionGate.eval rs xs).`2 by smt().
rewrite /reconstruct /eval /= /party_exec /=.

        have ->: map (fun (pid : pid_t) => (pid, let (_, sec) = oget (assoc xs pid) in let (x1, x2) = sec in fadd x1 x2)) pid_set = map (fun (pid : pid_t) => (pid, fadd (eval pid (update r 0 s)) (eval pid (update r' 0 s')))) pid_set.
          rewrite -(eq_in_map ((fun (pid : pid_t) => (pid, let (_, sec) = oget (assoc xs pid) in let (x1, x2) = sec in fadd x1 x2))) (fun (pid : pid_t) => (pid, fadd (eval pid (update r 0 s)) (eval pid (update r' 0 s'))))).
          move => x hx /=.
          move : H3 H7.
          by rewrite /share /= -!eq_in_map /sinput /AdditionFunctionality.input /#.
        have ->: (map (fun (pid : pid_t) => (pid, fadd (eval pid (update r 0 s)) (eval pid (update r' 0 s')))) pid_set) = (map (fun (pid : pid_t) => (pid, eval pid (add (update r 0 s) (update r' 0 s')))) pid_set).
          rewrite -eq_in_map => x hx /=.
          by rewrite eval_add.
        rewrite /reconstruct (interpolate_eval pid_set (add (update r 0 s) (update r' 0 s'))).
          by apply pid_set_uniq.
          by rewrite degree_add !degree_update0 H0 H4 pid_set_size /max /=; smt(t_pos).
        rewrite -update_add; first 2 by rewrite expo_diff_count //; rewrite ?H2 ?H7; smt(t_pos).
        rewrite !eval_update0 => //.
          rewrite expo_diff_count //; first by rewrite size_add; rewrite ?H2 ?H7; smt(t_pos).
          rewrite !size_add; first 2 by rewrite H1 /#.
          move => i hi; rewrite add_expos; first 3 by rewrite H1 /#. 
          by rewrite H2 /#. 
          by rewrite expo_diff_count //; first 2 by rewrite ?H2 ?H7; smt(t_pos).
          by rewrite expo_diff_count //; first 2 by rewrite H5; smt(t_pos).

rewrite /share /=.
rewrite -eq_in_map => pid; progress.
print eval_update0_add.
search (update).
rewrite -update_add.
search count.
rewrite expo_diff_count.
smt(expo_diff_count n_pos t_pos).
smt().
done.
smt(expo_diff_count n_pos t_pos).
rewrite eval_update0.
smt(expo_diff_count n_pos t_pos).
rewrite eval_update0.
smt(expo_diff_count n_pos t_pos).
done.
qed.

  op simulator (rs : rands_t) (xs : inputs_t) (cr : pid_t list) : AdditionGate.Gate.poutputs_t * (pid_t * (AdditionFunctionality.input_t * AdditionGate.Gate.rand_t * AdditionGate.Gate.in_messages_t)) list =
    let ys = map (fun pid => (pid, party_exec (rand pid rs) (input pid xs))) cr in
    let vs = (map (fun pid => (pid, (oget (assoc xs pid), (), []))) cr) in (ys, vs).

  clone import WeakSecurity as AddSec with 
    theory Gate <- AdditionGate.Gate,
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

end BGWAddition.
