require import Int IntDiv List Distr DList Real.

from General require import PrimeField ListExt FieldPolynomial.
from ArithmeticProtocol require import MultiplicationGate.
from Functionalities require import MultiplicationFunctionality.
from MPC require import GateWeak.
from SecretSharing require import Shamir.

theory BGWMultiplication.

  const n : {int | 3 <= n} as n_pos.
  const t : {int | 0 <= t < n%/2} as t_pos.

  clone import Shamir as HMShamir with
    op n = n,
    op t = t.

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
    (exists r s, valid_secret s /\ valid_rand r /\ share r s = sec1) /\ 
    (exists r' s', valid_secret s' /\ valid_rand r' /\ share r' s' = sec2).

  type rand_t = polynomial.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand (r : rand_t) : bool = HMShamir.valid_rand r.
  op valid_rands (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ (forall pid, pid \in pid_set => valid_rand (oget (assoc rs pid))).

  type output_t = secret_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  type msgs_t = t.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to (pid : pid_t) (ms : out_messages_t) : msgs_t = oget (assoc ms pid).
  op get_messages_from (pid : pid_t) (ms : in_messages_t) : msgs_t = oget (assoc ms pid).

  type trace_t = shares_t * in_messages_t.
  type traces_t = (pid_t * in_messages_t) list.
  op trace (pid : pid_t) (tr : traces_t) : in_messages_t = oget (assoc tr pid).
  
  type view_t = input_t * rand_t * trace_t.

  op party_exec1 (r : rand_t) (x : input_t) : (pid_t * share_t) list = 
    let (pub, sec) = x in
    let (sec1, sec2) = sec in HMShamir.share r (fmul sec1 sec2).

  op party_exec2 (ms : (pid_t * share_t) list) : output_t = 
    interpolate fzero ms.

  op out_messages_in_messages (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : out_messages_t = party_exec1 r x.

  op local_output_share (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : share_t =
    party_exec2 ims.

  op eval (rs : rands_t) (xs : inputs_t) : (pid_t * ((pid_t * msgs_t) list)) list * shares_t =
    let p1s = map (fun pid => (pid, party_exec1 (oget (assoc rs pid)) (oget (assoc xs pid)))) pid_set in
    let ms = map (fun pid => (pid, map (fun ms => let (sender, m) = ms in (sender, get_messages_to pid m)) p1s)) pid_set in 
    let p2s = map (fun pid => (pid, party_exec2 (oget (assoc ms pid)))) pid_set in
    (ms, p2s).

  clone import MultiplicationGate with
    op MultiplicationFunctionality.SecretSharingScheme.n = HMShamir.SecretSharingScheme.n,
    op MultiplicationFunctionality.SecretSharingScheme.t = HMShamir.SecretSharingScheme.t,
    type MultiplicationFunctionality.SecretSharingScheme.pid_t = HMShamir.SecretSharingScheme.pid_t,
    op MultiplicationFunctionality.SecretSharingScheme.pid_set = HMShamir.SecretSharingScheme.pid_set,
    op MultiplicationFunctionality.SecretSharingScheme.valid_secret = HMShamir.SecretSharingScheme.valid_secret,
    type MultiplicationFunctionality.SecretSharingScheme.share_t = HMShamir.SecretSharingScheme.share_t,
    type MultiplicationFunctionality.SecretSharingScheme.rand_t = HMShamir.SecretSharingScheme.rand_t,
    op MultiplicationFunctionality.SecretSharingScheme.valid_rand = HMShamir.SecretSharingScheme.valid_rand,
    op MultiplicationFunctionality.SecretSharingScheme.share = HMShamir.SecretSharingScheme.share,
    op MultiplicationFunctionality.SecretSharingScheme.public_encoding = HMShamir.SecretSharingScheme.public_encoding,
    op MultiplicationFunctionality.SecretSharingScheme.pub_reconstruct = HMShamir.SecretSharingScheme.pub_reconstruct,
    op MultiplicationFunctionality.SecretSharingScheme.reconstruct = HMShamir.SecretSharingScheme.reconstruct,
    op MultiplicationFunctionality.SecretSharingScheme.get_party_share = HMShamir.SecretSharingScheme.get_party_share,

    type rand_t = rand_t,
    op valid_rand = valid_rand,
    type msgs_t = msgs_t,
    op get_messages_to = get_messages_to,
    op get_messages_from = get_messages_from,
    op out_messages_in_messages = out_messages_in_messages,
    op local_output_share = local_output_share,
    op eval = eval
  proof *.
  realize MultiplicationFunctionality.GateFunctionality.n_pos by apply n_pos.
  realize MultiplicationFunctionality.GateFunctionality.t_pos by apply t_pos.
  realize MultiplicationFunctionality.GateFunctionality.pid_set_size by apply pid_set_size.
  realize MultiplicationFunctionality.GateFunctionality.pid_set_uniq by apply pid_set_uniq.
  realize Gate.GateFunctionality.n_pos by apply n_pos.
  realize Gate.GateFunctionality.t_pos by apply t_pos.
  realize MultiplicationFunctionality.SecretSharingScheme.n_pos by apply n_pos.
  realize MultiplicationFunctionality.SecretSharingScheme.t_pos by apply t_pos.
  realize MultiplicationFunctionality.SecretSharingScheme.pid_set_size by apply pid_set_size.
  realize MultiplicationFunctionality.SecretSharingScheme.pid_set_uniq by apply pid_set_uniq.
  realize MultiplicationFunctionality.SecretSharingScheme.correct by move : HMShamir.SecretSharingScheme.correct => /#.
  realize MultiplicationFunctionality.SecretSharingScheme.size_share by move : HMShamir.SecretSharingScheme.size_share => /#.
  realize MultiplicationFunctionality.SecretSharingScheme.unzip1_share by move : HMShamir.SecretSharingScheme.unzip1_share => /#.
  realize MultiplicationFunctionality.SecretSharingScheme.public_encoding_correct by move : HMShamir.SecretSharingScheme.public_encoding_correct => /#.
  realize MultiplicationFunctionality.SecretSharingScheme.size_public_encoding by move : HMShamir.SecretSharingScheme.size_public_encoding => /#.
  realize MultiplicationFunctionality.SecretSharingScheme.unzip1_public_encoding by move : HMShamir.SecretSharingScheme.unzip1_public_encoding => /#.
  realize MultiplicationFunctionality.SecretSharingScheme.public_encoding_inj by move : HMShamir.SecretSharingScheme.public_encoding_inj => /#.
  realize MultiplicationFunctionality.SecretSharingScheme.public_encoding_reconstruct by move : HMShamir.SecretSharingScheme.public_encoding_reconstruct => /#.
  realize MultiplicationFunctionality.SecretSharingScheme.public_encoding_rand by move : HMShamir.SecretSharingScheme.public_encoding_rand => /#.
  realize eval_domain.
rewrite /eval /=; progress.
by rewrite -map_comp /(\o) /= map_id //=.
  qed.
  realize local_output_share_correct.
rewrite /eval /= /party_exec2.
progress.
rewrite !map_assoc //=.
by rewrite !map_assoc //=.
  qed.
  realize out_messages_in_messages_consistency.
rewrite /gate /eval /= /party_exec1.
progress.
rewrite /get_messages_to /= /get_messages_from /= /trace /=.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
rewrite /rand /=.
rewrite /out_messages_in_messages /= /party_exec1 /input /=.
rewrite -map_comp /(\o) /=.
by rewrite !map_assoc //=.
  qed.  
  realize Gate.correct.
    rewrite /valid_input /valid_inputs /valid_rands /valid_rand /valid_secret /sinput /input /output_pred /gate /eval /f /party_exec1 /party_exec2 /HMShamir.SecretSharingScheme.pid_set /reconstruct /sinput /input /input_pred. 
    move => rs xs /=. progress.
    move : H3 H7; rewrite /share /= -!eq_in_map => /> H3 H7; progress.
    have ->: (map (fun (pid1 : pid_t) => (pid1, let (_, sec) = oget (assoc xs pid1) in let (sec1, sec2) = sec in map (fun (pid2 : coeficient) => (pid2, eval pid2 (update (oget (assoc rs pid1)) 0 (fmul sec1 sec2)))) pid_set)) pid_set) = (map (fun (pid1 : pid_t) => (pid1, (share (oget (assoc rs pid1)) (fmul (eval pid1 (update r 0 s)) (eval pid1 (update r' 0 s')))))) pid_set).
      rewrite -(eq_in_map) => pid hxpid /=.
      rewrite /share /= /sinput.
      rewrite H3 // H7 //=. 
      have : exists pub sec, (pub, sec) = oget (assoc xs pid)
        by exists (oget (assoc xs pid)).`1 (oget (assoc xs pid)).`2 => /#.
      progress. rewrite -H11 /=; move : H11.
      elim sec => sec1 sec2 /=; progress.
    have ->: (map (fun (pid : pid_t) => (pid, interpolate fzero (oget (assoc (map (fun (pid0 : pid_t) => (pid0, map (fun (ms : pid_t * BGWMultiplication.out_messages_t) => let (sender, m) = ms in (sender, (BGWMultiplication.get_messages_to pid0 m))) (map (fun (pid1 : pid_t) => (pid1,  share (oget (assoc rs pid1)) (fmul (eval pid1 (update r 0 s)) (eval pid1 (update r' 0 s'))))) pid_set))) pid_set) pid)))) pid_set) = (map (fun (pid : pid_t) => (pid, interpolate fzero (oget (assoc (map (fun (pid0 : pid_t) => (pid0, map ((fun (ms : pid_t * BGWMultiplication.out_messages_t) => let (sender, m) = ms in (sender, (BGWMultiplication.get_messages_to pid0 m))) \o (fun (pid1 : pid_t) => (pid1,  share (oget (assoc rs pid1)) (fmul (eval pid1 (update r 0 s)) (eval pid1 (update r' 0 s')))))) pid_set)) pid_set) pid)))) pid_set).
        rewrite -eq_in_map; progress.
        do 3! congr => /=.
        by congr; rewrite fun_ext /(==); progress; rewrite -map_comp.
    rewrite /(\o) => /=.
    have ->: (map (fun (pid : pid_t) => (pid, interpolate fzero (oget (assoc (map (fun (pid0 : pid_t) => (pid0, map (fun (x : pid_t) => (x, (BGWMultiplication.get_messages_to pid0 (share (oget (assoc rs x)) (fmul (eval x (update r 0 s)) (eval x (update r' 0 s'))))))) pid_set)) pid_set) pid)))) pid_set) = (map (fun (pid : pid_t) => (pid, interpolate fzero (oget (Some ((fun pid0 => (map (fun (x : pid_t) => (x, (BGWMultiplication.get_messages_to pid0 (share (oget (assoc rs x)) (fmul (eval x (update r 0 s)) (eval x (update r' 0 s'))))))) pid_set)) pid))))) pid_set).
      by rewrite -eq_in_map; progress; rewrite map_assoc.
    rewrite /get_messages_to /share /=.
    have ->: (map (fun (pid : pid_t) => (pid, interpolate fzero (map (fun (x : pid_t) => (x, odflt witness (assoc (map (fun (pid0 : coeficient) => (pid0, eval pid0 (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set) pid))) pid_set))) pid_set) = (map (fun (pid : pid_t) => (pid, interpolate fzero (map (fun (x : pid_t) => (x,odflt witness (Some ((fun pid0 => eval pid0 (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s'))))) pid)))) pid_set))) pid_set).
      rewrite -eq_in_map; progress; congr.
      by rewrite -eq_in_map; progress; rewrite map_assoc /=.
    simplify. 
    have ->: (map (fun (pid : Shamir.pid_t) => (pid, (oget (assoc xs pid)).`2.`1)) pid_set) = (map (fun (pid : Shamir.pid_t) => (pid, eval pid (update r 0 s))) pid_set).
      by rewrite -eq_in_map => pid; progress; rewrite H3 /=.
    have ->: (map (fun (pid : Shamir.pid_t) => (pid, (oget (assoc xs pid)).`2.`2)) pid_set) = (map (fun (pid : Shamir.pid_t) => (pid, eval pid (update r' 0 s'))) pid_set).
      by rewrite -eq_in_map => pid; progress; rewrite H7 /=.
    rewrite !interpolate_eval; first by rewrite pid_set_uniq.
      * by rewrite degree_update0; first by smt(pid_set_size n_pos t_pos).
      * by rewrite pid_set_uniq.
      * by rewrite degree_update0; first by smt(pid_set_size n_pos t_pos).
    have : interpolate fzero (map (fun (pid : pid_t) => (pid, interpolate fzero (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set))) pid_set) = fmul (eval fzero (update r 0 s)) (eval fzero (update r' 0 s')).
      rewrite /interpolate /=.
      have ->: (interpolate_loop fzero (unzip1 (map (fun (pid : pid_t) => (pid, sumt (interpolate_loop fzero (unzip1 (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set)) (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set)))) pid_set)) (map (fun (pid : pid_t) => (pid, foldr (fun (x y : t) => fadd x y) fzero (interpolate_loop fzero (unzip1 (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set)) (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set)))) pid_set)) = (interpolate_loop fzero pid_set (map (fun (pid : pid_t) => (pid, sumt (interpolate_loop fzero pid_set (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set)))) pid_set)).
        rewrite !unzip1_map_assoc /=; do 2! congr.
        by rewrite fun_ext /(==); progress; rewrite !unzip1_map_assoc /=.
      (*have ->: sumt (interpolate_loop fzero Gate.pid_set (map (fun (pid : coeficient) => (pid, eval pid (update r 0 s))) pid_set)) = (sumt (interpolate_loop fzero pid_set (map (fun (pid : coeficient) => (pid, eval pid (update r 0 s))) pid_set))).
        by do 2! congr; rewrite !unzip1_map_assoc /=.*)
      (*have ->: (sumt (interpolate_loop fzero (unzip1 (map (fun (pid : coeficient) => (pid, eval pid (update r' 0 s'))) pid_set)) (map (fun (pid : coeficient) => (pid, eval pid (update r' 0 s'))) pid_set))) = (sumt (interpolate_loop fzero pid_set (map (fun (pid : coeficient) => (pid, eval pid (update r' 0 s'))) pid_set))).
        by do 2! congr; rewrite !unzip1_map_assoc /=.*)
      rewrite /interpolate_loop /= -!map_comp /(\o) /=.
      have ->: (fun (x : pid_t) => fmul (basis fzero x pid_set) (sumt (map (fun (xy : t * t) => fmul (basis fzero xy.`1 pid_set) xy.`2) (map (fun (x0 : pid_t) => (x0, eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s')))))) pid_set)))) = (fun (x : pid_t) => fmul (basis fzero x pid_set) (sumt (map ((fun (xy : t * t) => fmul (basis fzero xy.`1 pid_set) xy.`2) \o (fun (x0 : pid_t) => (x0, eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s'))))))) pid_set))).
        by rewrite fun_ext /(==); progress; congr; rewrite -map_comp.
      rewrite /(\o) /=.
      have ->: (fun (x : pid_t) => fmul (basis fzero x pid_set) (sumt (map (fun (x0 : pid_t) => fmul (basis fzero x0 pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s')))))) pid_set))) = (fun (x : pid_t) => (sumt (map (fun y => fmul (basis fzero x pid_set) y) (map (fun (x0 : pid_t) => fmul (basis fzero x0 pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s')))))) pid_set)))).
        by rewrite fun_ext /(==); progress; rewrite sumt_distr.
      have ->: (fun (x : pid_t) => sumt (map (fun (y : t) => fmul (basis fzero x pid_set) y) (map (fun (x0 : pid_t) => fmul (basis fzero x0 pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s')))))) pid_set))) = (fun (x : pid_t) => sumt (map ((fun (y : t) => fmul (basis fzero x pid_set) y) \o (fun (x0 : pid_t) => fmul (basis fzero x0 pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s'))))))) pid_set)).
        by rewrite fun_ext /(==); progress; rewrite map_comp.
      rewrite /(\o) /=.
      have ->: (fun (x : pid_t) => sumt (map (fun (x0 : pid_t) => fmul (basis fzero x pid_set) (fmul (basis fzero x0 pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s'))))))) pid_set)) = (fun (x : pid_t) => sumt (map (fun (x0 : pid_t) => fmul (basis fzero x0 pid_set) (fmul (basis fzero x pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s'))))))) pid_set)).
        rewrite fun_ext /(==); progress; do 2! congr.
        by rewrite fun_ext /(==); progress; ringeq.
      have ->: sumt (map (fun (x : pid_t) => sumt (map (fun (x0 : pid_t) => fmul (basis fzero x0 pid_set) (fmul (basis fzero x pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s'))))))) pid_set)) pid_set) = sumt (map (fun (x0 : pid_t) => sumt (map (fun (x : pid_t) => fmul (basis fzero x0 pid_set) (fmul (basis fzero x pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s'))))))) pid_set)) pid_set).
        by rewrite sumt_comm_assoc. 
      have ->: (fun (x0 : pid_t) => sumt (map (fun (x : pid_t) => fmul (basis fzero x0 pid_set) (fmul (basis fzero x pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s'))))))) pid_set)) = (fun (x0 : pid_t) => fmul (basis fzero x0 pid_set) (sumt (map (fun (x : pid_t) => (fmul (basis fzero x pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s'))))))) pid_set))).
        by rewrite fun_ext /(==); progress; rewrite sumt_distr /= -map_comp /(\o) /=.
      have ->: sumt (map (fun (x0 : pid_t) => fmul (basis fzero x0 pid_set) (sumt (map (fun (x : pid_t) => fmul (basis fzero x pid_set) (eval x (update (oget (assoc rs x0)) 0 (fmul (eval x0 (update r 0 s)) (eval x0 (update r' 0 s')))))) pid_set))) pid_set) = interpolate fzero (map (fun (x : pid_t) => (x, interpolate fzero (map (fun (pid : pid_t) => (pid, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set))) pid_set).
        rewrite /interpolate !unzip1_map_assoc /interpolate_loop -!map_comp /(\o) /=.
        do 2! congr; rewrite fun_ext /(==); progress.
        do 2! congr; rewrite -map_comp /(\o) /=.
        by congr; rewrite fun_ext /(==); progress; rewrite !unzip1_map_assoc.
      have ->: interpolate fzero (map (fun (x : pid_t) => (x, interpolate fzero (map (fun (pid : pid_t) => (pid, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set))) pid_set) = interpolate fzero (map (fun (x : pid_t) => (x, eval fzero (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set).
        congr; rewrite -eq_in_map; progress.
        rewrite interpolate_eval //; first by rewrite pid_set_uniq.
          rewrite degree_update0 pid_set_size.
          move : (H9 (x0)).
          rewrite H11 /=; progress; rewrite H12 /t /n; smt(t_pos).
      have ->: (map (fun (x : pid_t) => (x, eval fzero (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set) = (map (fun (x : pid_t) => (x, eval x (mul (update r 0 s) (update r' 0 s')) )) pid_set).
        rewrite -eq_in_map; progress; rewrite eval_update0.
        move : (H9 (x0)).
        rewrite H11 expo_diff_count //; first 2 by smt(t_pos).
        by rewrite eval_mul.
      rewrite interpolate_eval; first by apply pid_set_uniq.
        rewrite degree_mul !degree_update0 H0 H4 /t /n pid_set_size; smt.
      by rewrite !eval_mul !eval_update0; first 2 by rewrite expo_diff_count; smt(t_pos). 
    by done. 
  qed.
  realize Gate.local_output_correct.
    rewrite /local_output /output /gate /eval /party_exec1 /party_exec2 /input 
            /pid_set /BGWMultiplication.get_messages_to /trace => />; progress; rewrite !map_assoc //=.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
  qed.
  realize Gate.messages_consistency.
    rewrite /local_output /output /gate /eval /party_exec1 /party_exec2 /input 
            /pid_set /get_messages_to /out_messages /trace /party_exec1 => />; progress. 
    rewrite /get_messages_from !map_assoc /share //= /trace /= !map_assoc /out_messages_in_messages //= -!map_comp /(\o) /= !map_assoc //=.
  qed.
  realize Gate.correct_domain.
    by move => rs xs; rewrite /gate /eval /= /party_exec -!map_comp /(\o) /= !map_id /pid_set.
  qed.
  realize eval_preserves_share.
rewrite /valid_inputs /valid_rands /eval /pid_set /sinput /pinput /input /valid_secret /valid_rand.
progress.
rewrite /party_exec2 /party_exec1 /= /reconstruct /=.

    move : H3 H7; rewrite /share /= -!eq_in_map => /> H3 H7; progress.
    have ->: (map (fun (pid1 : pid_t) => (pid1, let (_, sec) = oget (assoc xs pid1) in let (sec1, sec2) = sec in map (fun (pid2 : coeficient) => (pid2, eval pid2 (update (oget (assoc rs pid1)) 0 (fmul sec1 sec2)))) pid_set)) pid_set) = (map (fun (pid1 : pid_t) => (pid1, (share (oget (assoc rs pid1)) (fmul (eval pid1 (update r 0 s)) (eval pid1 (update r' 0 s')))))) pid_set).
      rewrite -(eq_in_map) => pid hxpid /=.
      rewrite /share /= /sinput.
      rewrite H3 // H7 //=. 
      have : exists pub sec, (pub, sec) = oget (assoc xs pid)
        by exists (oget (assoc xs pid)).`1 (oget (assoc xs pid)).`2 => /#.
      progress. rewrite -H10 /=; move : H10.
      elim sec => sec1 sec2 /=; progress.

    have ->: (map (fun (pid : pid_t) => (pid, interpolate fzero (oget (assoc (map (fun (pid0 : pid_t) => (pid0, map (fun (ms : pid_t * BGWMultiplication.out_messages_t) => let (sender, m) = ms in (sender, (BGWMultiplication.get_messages_to pid0 m))) (map (fun (pid1 : pid_t) => (pid1,  share (oget (assoc rs pid1)) (fmul (eval pid1 (update r 0 s)) (eval pid1 (update r' 0 s'))))) pid_set))) pid_set) pid)))) pid_set) = (map (fun (pid : pid_t) => (pid, interpolate fzero (oget (assoc (map (fun (pid0 : pid_t) => (pid0, map ((fun (ms : pid_t * BGWMultiplication.out_messages_t) => let (sender, m) = ms in (sender, (BGWMultiplication.get_messages_to pid0 m))) \o (fun (pid1 : pid_t) => (pid1,  share (oget (assoc rs pid1)) (fmul (eval pid1 (update r 0 s)) (eval pid1 (update r' 0 s')))))) pid_set)) pid_set) pid)))) pid_set).
        rewrite -eq_in_map; progress.
        do 3! congr => /=.
        by congr; rewrite fun_ext /(==); progress; rewrite -map_comp.
    rewrite /(\o) => /=.
    have ->: (map (fun (pid : pid_t) => (pid, interpolate fzero (oget (assoc (map (fun (pid0 : pid_t) => (pid0, map (fun (x : pid_t) => (x, (BGWMultiplication.get_messages_to pid0 (share (oget (assoc rs x)) (fmul (eval x (update r 0 s)) (eval x (update r' 0 s'))))))) pid_set)) pid_set) pid)))) pid_set) = (map (fun (pid : pid_t) => (pid, interpolate fzero (oget (Some ((fun pid0 => (map (fun (x : pid_t) => (x, (BGWMultiplication.get_messages_to pid0 (share (oget (assoc rs x)) (fmul (eval x (update r 0 s)) (eval x (update r' 0 s'))))))) pid_set)) pid))))) pid_set).
      by rewrite -eq_in_map; progress; rewrite map_assoc.
    rewrite /get_messages_to /share /=.
    have ->: (map (fun (pid : pid_t) => (pid, interpolate fzero (map (fun (x : pid_t) => (x, odflt witness (assoc (map (fun (pid0 : coeficient) => (pid0, eval pid0 (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set) pid))) pid_set))) pid_set) = (map (fun (pid : pid_t) => (pid, interpolate fzero (map (fun (x : pid_t) => (x,odflt witness (Some ((fun pid0 => eval pid0 (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s'))))) pid)))) pid_set))) pid_set).
      rewrite -eq_in_map; progress; congr.
      by rewrite -eq_in_map; progress; rewrite map_assoc /=.
    simplify. 

progress.

    have H13 : degree (interpolate_poly (map (fun (pid : coeficient) => (pid, eval fzero (interpolate_poly (map (fun (pid' : pid_t) => (pid', eval pid (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set)))) pid_set)) = HMShamir.t.
      rewrite -(degree_interpolate_poly0 pid_set (map (fun pid => (pid, interpolate_poly (map (fun (pid' : pid_t) => (pid', eval pid (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set))) pid_set) HMShamir.t).
        by rewrite pid_set_uniq /=.
        by rewrite -map_comp /(\o) map_id.
        progress; rewrite map_assoc //=.
        rewrite -(degree_interpolate_polyX pid_set (map (fun x => (x, (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set) x HMShamir.t).
          by rewrite pid_set_uniq /=.
          by rewrite -map_comp /(\o) map_id /=.
          by progress; rewrite map_assoc //= degree_update0 /#.
        by do 2!congr; rewrite -eq_in_map; progress; rewrite map_assoc //=.
      do 2!congr.
      by rewrite -eq_in_map; progress; rewrite map_assoc //=.
    have H14 : size (interpolate_poly (map (fun (pid : coeficient) => (pid, eval fzero (interpolate_poly (map (fun (pid' : pid_t) => (pid', eval pid (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set)))) pid_set)) = HMShamir.t + 1.
      rewrite -(size_interpolate_polyX pid_set (map (fun (pid : coeficient) => (pid, (interpolate_poly (map (fun (pid' : pid_t) => (pid', eval pid (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set)))) pid_set) fzero (HMShamir.t + 1)).
        by rewrite pid_set_uniq. 
        by rewrite -map_comp /(\o) map_id.
        move => pid H15; rewrite map_assoc //=.
        rewrite -(size_interpolate_polyX pid_set (map (fun (pid' : pid_t) => (pid', (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set) pid (HMShamir.t + 1)).
          by rewrite pid_set_uniq. 
          by rewrite -map_comp /(\o) map_id.
          by move => pid' H14; rewrite map_assoc //= size_update0 => /#.
        by do 2!congr; rewrite -eq_in_map; progress; rewrite map_assoc //=.
      by do 2!congr; rewrite -eq_in_map; progress; rewrite map_assoc //=.
    have H15 : forall (i : int), 0 <= i && i < HMShamir.t + 1 => (nth mzero (interpolate_poly (map (fun (pid : coeficient) => (pid, eval fzero (interpolate_poly (map (fun (pid' : pid_t) => (pid', eval pid (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set)))) pid_set)) i).`expo = HMShamir.t - i.
      progress.
      rewrite -(expos_interpolate_polyX pid_set (map (fun (pid : coeficient) => (pid, (interpolate_poly (map (fun (pid' : pid_t) => (pid', eval pid (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set)))) pid_set) fzero (HMShamir.t+1)).
        by rewrite pid_set_uniq. 
        by rewrite -map_comp /(\o) map_id.
        move => pid; progress; rewrite map_assoc //=.
        rewrite -(size_interpolate_polyX pid_set (map (fun (pid' : pid_t) => (pid', (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set) pid (HMShamir.t+1)).
          by rewrite pid_set_uniq. 
          by rewrite -map_comp /(\o) map_id.
          by move => pid'; progress; rewrite map_assoc //= size_update0 => /#.
        by do 2!congr; rewrite -eq_in_map; progress; rewrite map_assoc //=.
      progress; rewrite map_assoc //=.
      rewrite -(expos_interpolate_polyX pid_set (map (fun (pid' : pid_t) => (pid', (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set) x (HMShamir.t+1)).
        by rewrite pid_set_uniq. 
        by rewrite -map_comp /(\o) map_id.
        by move => pid'; progress; rewrite !map_assoc //= size_update0 => /#.
progress.
rewrite !map_assoc //=.
rewrite update_expo => /#.
        by smt().
        by do 3!congr; rewrite -eq_in_map; progress; rewrite map_assoc //=.
        by smt().
      by do 3!congr; rewrite -eq_in_map; progress; rewrite map_assoc //=.


    exists (interpolate_poly (map (fun pid => (pid, interpolate fzero (map (fun pid' => (pid', eval pid (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set))) pid_set)); split. 
      rewrite /valid_rand /=. 
      have ->: (map (fun (pid : coeficient) => (pid, interpolate fzero (map (fun (pid' : pid_t) => (pid', eval pid (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set))) pid_set) = (map (fun (pid : coeficient) => (pid, eval fzero (interpolate_poly (map (fun (pid' : pid_t) => (pid', eval pid (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set)))) pid_set)
        by rewrite -eq_in_map; progress; rewrite interpolate_poly_eval; first rewrite uniq_assoc -map_comp /(\o) /= map_id pid_set_uniq.
      by done. 
    rewrite -eq_in_map => pid; progress.
    have ->: (map (fun (pid0 : coeficient) => (pid0, interpolate fzero (map (fun (pid' : pid_t) => (pid', eval pid0 (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set))) pid_set) = (map (fun (pid0 : coeficient) => (pid0, eval fzero (interpolate_poly (map (fun (pid' : pid_t) => (pid', eval pid0 (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set)))) pid_set).
      rewrite -eq_in_map; progress.
      by rewrite interpolate_poly_eval; first
        by rewrite uniq_assoc; first by rewrite -map_comp /(\o) map_id pid_set_uniq.
    rewrite eval_update.
      rewrite expo_diff_count //.
        by rewrite H14; smt (t_pos).
        by rewrite H14; progress; rewrite H15. 
      rewrite get_monomial0 //.
        rewrite expo_diff_count //. 
          by rewrite H14; smt (t_pos).
          by rewrite H14; progress; rewrite H15. 
    rewrite /meval /= !pow0 -(interpolate_poly_eval _ fzero); first by
      by rewrite uniq_assoc; first by rewrite -map_comp /(\o) map_id pid_set_uniq.
    rewrite !mulf1 -interpolate_poly_eval; first 
      by rewrite uniq_assoc -map_comp /(\o) map_id pid_set_uniq.
    rewrite interpolate_mem.
      by rewrite -map_comp /(\o) map_id pid_set_uniq.
      by rewrite -map_comp /(\o) map_id.
    rewrite map_assoc //=.
    have ->: (map (fun (pid0 : coeficient) => (pid0, eval fzero (interpolate_poly (map (fun (pid' : pid_t) => (pid', eval pid0 (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set)))) pid_set) = (map (fun (pid0 : coeficient) => (pid0, interpolate fzero (map (fun (pid' : pid_t) => (pid', eval pid0 (update (oget (assoc rs pid')) 0 (fmul (eval pid' (update r 0 s)) (eval pid' (update r' 0 s')))))) pid_set))) pid_set).
      rewrite -eq_in_map; progress.
      by rewrite interpolate_poly_eval //; first 
        by rewrite uniq_assoc -map_comp /(\o) map_id pid_set_uniq.
    rewrite -interpolate_poly_eval; first by
      rewrite uniq_assoc -map_comp /(\o) map_id pid_set_uniq.
    ringeq.
qed.

  op simulator (rs : rands_t) (xs : inputs_t) (cr : pid_t list) : 
    MultiplicationGate.Gate.poutputs_t * 
    (pid_t * (MultiplicationFunctionality.input_t * 
              MultiplicationGate.Gate.rand_t * 
              MultiplicationGate.Gate.in_messages_t)) list =
    let pub = fst (oget (assoc xs (head witness cr))) in
    let xs' = map (fun pid => (pid, if pid \in cr then oget (assoc xs pid) else (pub, (fzero, fzero)))) pid_set in
    let (tr,ys) = eval rs xs' in
    (map (fun pid => (pid, output pid ys)) cr,
     map (fun pid => (pid, (oget (assoc xs pid), oget (assoc rs pid), oget (assoc tr pid)))) cr).

  clone import WeakSecurity as MulSec with 
    theory Gate <- MultiplicationGate.Gate,
    op simulator = simulator.

  section Security.

    declare module D : Distinguisher_t{RealEvaluator,IdealEvaluator}.

    module R : Rand_t = {
      proc gen(aux : aux_t, cr : pid_t list) : rands_t = {
        var p, pid, i, ps;
        i <- 0; ps <- [];

        while (i < n) {

          pid <- nth witness pid_set i;

          if (pid \in cr) {
            p <$ dpolynomial t;
          }
          else {
            p <@ PolynomialRand.gen(t);
          }
          ps <- ps ++ [(pid,p)];
          i <- i + 1;
        }
        return ps;
      }
    }.

    lemma rand_srand_equiv cr_ : 
      equiv [ R.gen ~ R.gen : ={aux,cr} /\ cr_ = cr{2} /\ (forall pid, pid \in cr{2} => pid \in pid_set) ==> 
                 unzip1 res{1} = pid_set /\ unzip1 res{1} = unzip1 res{2} /\
                 (forall pid, pid \in pid_set => 
                   if pid \in cr_ then oget (assoc res{1} pid) = oget (assoc res{2} pid)
                   else  (forall x c c', x <> fzero => eval x (update (oget (assoc res{1} pid)) 0 c) = eval x (update (oget (assoc res{2} pid)) 0 c'))) /\
                 (forall pid, pid \in pid_set => oget (assoc res{1} pid) \in dpolynomial t) /\
                 (forall pid, pid \in pid_set => oget (assoc res{2} pid) \in dpolynomial t) ].
    proof.
      proc; sp.
      while (={i,aux,cr} /\ 0 <= i{1} <= n /\ (forall pid, pid \in cr{2} => pid \in pid_set) /\
            (unzip1 ps{1} = take i{1} pid_set) /\ cr_ = cr{2} /\ unzip1 ps{1} = unzip1 ps{2} /\
            (forall pid, pid \in unzip1 ps{1} => if pid \in cr_ then 
                                                   oget (assoc ps{1} pid) = oget (assoc ps{2} pid)
                                                else (forall x c c', x <> fzero => eval x (update (oget (assoc ps{1} pid)) 0 c) = eval x (update (oget (assoc ps{2} pid)) 0 c'))) /\
            (forall pid, pid \in unzip1 ps{1} => oget (assoc ps{1} pid) \in dpolynomial t) /\
            (forall pid, pid \in unzip1 ps{2} => oget (assoc ps{2} pid) \in dpolynomial t)).
        wp; sp; if => //.
          wp; rnd; wp; skip; progress; first 2 by smt().
            rewrite map_cat /= (take_nth witness); first by rewrite pid_set_size.
            by smt(@List).
            by rewrite !map_cat H3.
            rewrite !assoc_cat; move : H12.
            rewrite mapP /=; progress.
            move : H12; rewrite mem_cat; progress.
            case (x \in ps{1}); progress; first by smt().
            case (x.`1 \in unzip1 ps{1}); progress; first by smt().
            have ->: x.`1 \in unzip1 ps{2} <=> false; first by smt().
            by simplify.
            rewrite !assoc_cat; move : H12.
            rewrite mapP /=; progress.
            move : H12; rewrite mem_cat; progress.
            case (x0 \in ps{1}); progress.
              rewrite -H3.
              have ->: x0.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x0.
              simplify; move : (H4 x0.`1).
              have ->: x0.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x0.
              simplify; rewrite H13 /=; progress.
              by move : (H16 x c c') => /#.
            case (x0.`1 \in unzip1 ps{1}); progress.
              rewrite -H3 H16 /=.
              simplify; move : (H4 x0.`1).
              simplify; rewrite H16 H13 /=; progress.
              by move : (H17 x c c') => /#.
            rewrite -H3 H16 /=.
            simplify; move : (H4 x0.`1).
            simplify; rewrite H16 H13 /=; progress.
            by smt().
            rewrite !assoc_cat; move : H12.
            rewrite mapP /=; progress.
            move : H12; rewrite mem_cat; progress.
            case (x \in ps{1}); progress.
              have ->: x.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x.
              by simplify; rewrite H5 mapP; progress; exists x.
            case (x.`1 \in unzip1 ps{1}); progress; first by rewrite H5.
            by smt().
            rewrite !assoc_cat; move : H12.
            rewrite mapP /=; progress.
            move : H12; rewrite mem_cat; progress.
            case (x \in ps{2}); progress.
              have ->: x.`1 \in unzip1 ps{2} by rewrite mapP; progress; exists x.
              by simplify; rewrite H6 mapP; progress; exists x.
            case (x.`1 \in unzip1 ps{2}); progress; first by rewrite H6.
            by smt().
          call (polynomial_rand_equiv t); skip; progress; first 2 by smt().
            rewrite map_cat /= (take_nth witness); first by rewrite pid_set_size.
            by smt(@List).
            by rewrite !map_cat H3.
            rewrite !assoc_cat; move : H13.
            rewrite mapP /=; progress.
            move : H13; rewrite mem_cat; progress.
            case (x \in ps{1}); progress; first by smt().
            case (x.`1 \in unzip1 ps{1}); progress; first by smt().
            have ->: x.`1 \in unzip1 ps{2} <=> false; first by smt().
            by smt().
            rewrite !assoc_cat; move : H13.
            rewrite mapP /=; progress.
            move : H13; rewrite mem_cat; progress.
            case (x0 \in ps{1}); progress.
              rewrite -H3.
              have ->: x0.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x0.
              simplify; move : (H4 x0.`1).
              have ->: x0.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x0.
              simplify; rewrite H14 /=; progress.
              by move : (H17 x c c') => /#.
            case (x0.`1 \in unzip1 ps{1}); progress.
              rewrite -H3 H17 /=.
              simplify; move : (H4 x0.`1).
              simplify; rewrite H17 H14 /=; progress.
              by move : (H18 x c c') => /#.
            rewrite -H3 H17 /=.
            simplify; move : (H4 x0.`1).
            simplify; rewrite H17 H14 /=; progress.
            by smt().
            rewrite !assoc_cat; move : H13.
            rewrite mapP /=; progress.
            move : H13; rewrite mem_cat; progress.
            case (x \in ps{1}); progress.
              have ->: x.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x.
              by simplify; rewrite H5 mapP; progress; exists x.
            case (x.`1 \in unzip1 ps{1}); progress; first by rewrite H5.
            by smt().
            rewrite !assoc_cat; move : H13.
            rewrite mapP /=; progress.
            move : H13; rewrite mem_cat; progress.
            case (x \in ps{2}); progress.
              have ->: x.`1 \in unzip1 ps{2} by rewrite mapP; progress; exists x.
              by simplify; rewrite H6 mapP; progress; exists x.
            case (x.`1 \in unzip1 ps{2}); progress; first by rewrite H6.
            by smt().
        skip; progress.
          by smt(n_pos).
          by rewrite take0.
          by rewrite H5 take_oversize; smt(pid_set_size).
          move : (H7 pid0); rewrite H5.
          have ->: take i_R pid_set = pid_set by rewrite take_oversize; smt(pid_set_size).
          by rewrite H10 H11 /=.
          move : (H7 pid0); rewrite H5.
          have ->: take i_R pid_set = pid_set by rewrite take_oversize; smt(pid_set_size).
          by rewrite H10 H11 /=; progress; rewrite (H13 x c c').
          by rewrite H8 H5 take_oversize; smt(pid_set_size).
          by rewrite H9 -H6 H5 take_oversize; smt(pid_set_size).
    qed.

    equiv real_ideal_equiv :
      GameReal(D,R).main ~ GameIdeal(D,R).main :
      ={glob D, glob R, aux, x} ==> ={res}.
    proof.
      proc. 
      seq 1 1 : (#pre /\ ={xs,cr}); first by call (_ : true).
      case (valid_corrupted_set cr{2}); last first.
rcondf{1} 2.
progress.
inline*.
wp.
while (#pre).
sp.
if.
by wp; rnd; skip; progress.
by wp; rnd; wp; skip; progress.
by wp; skip; progress => /#.
rcondf{2} 2.
progress.
inline*.
wp.
while (#pre).
sp.
if.
by wp; rnd; skip; progress.
by wp; rnd; wp; skip; progress.
by wp; skip; progress => /#.
inline*.
rnd.
wp.
sp 2 2.
while (#pre /\ ={i}).
sp.
if.
by progress.
by wp; rnd; skip; progress.
by wp; rnd; wp; skip; progress.
by wp; skip; progress => /#.
      seq 1 1 : (#pre /\ 
                 (forall pid, pid \in pid_set => 
                   if pid \in cr{2} then oget (assoc r{1} pid) = oget (assoc r{2} pid)
                   else  (forall x c c', x <> fzero => eval x (update (oget (assoc r{1} pid)) 0 c) = eval x (update (oget (assoc r{2} pid)) 0 c'))) /\
                 unzip1 r{1} = pid_set /\ unzip1 r{1} = unzip1 r{2} /\
                 (forall pid, pid \in pid_set => oget (assoc r{1} pid) \in dpolynomial t) /\
                 (forall pid, pid \in pid_set => oget (assoc r{2} pid) \in dpolynomial t)).
        exists* cr{2}; elim* => cr.
        by call (rand_srand_equiv cr); skip; progress => /#.
      if; last by rnd.
        progress.
          by rewrite -H2 H1.
          move : H5; rewrite /valid_rands /valid_rand => [[H5]] H9.
            rewrite /BGWMultiplication.HMShamir.t (dpolynomial_degree (oget (assoc r{2} pid)) BGWMultiplication.t) //.
              by smt(t_pos).
              by rewrite H4 //.
            rewrite /BGWMultiplication.HMShamir.t (dpolynomial_size (oget (assoc r{2} pid)) BGWMultiplication.t) //.
              by smt(t_pos).
              by rewrite H4 //.
            rewrite /BGWMultiplication.HMShamir.t (dpolynomial_exp (oget (assoc r{2} pid)) BGWMultiplication.t) //.
              by smt(t_pos).
              by rewrite H4 //.
          by rewrite H1.
          move : H5; rewrite /valid_rands /valid_rand => [[H5]] H9.
            rewrite /BGWMultiplication.HMShamir.t (dpolynomial_degree (oget (assoc r{1} pid)) BGWMultiplication.t) //.
              by smt(t_pos).
              by rewrite H3 //.
            rewrite /BGWMultiplication.HMShamir.t (dpolynomial_size (oget (assoc r{1} pid)) BGWMultiplication.t) //.
              by smt(t_pos).
              by rewrite H3 //.
            rewrite /BGWMultiplication.HMShamir.t (dpolynomial_exp (oget (assoc r{1} pid)) BGWMultiplication.t) //.
              by smt(t_pos).
              by rewrite H3 //.

      inline *; call (_ : true); wp; skip; progress.
       rewrite /simulator /= /gate /eval /party_exec1 /party_exec2 /= /input /= /output /get_messages_to /=.

rewrite -eq_in_map => pid; progress.
rewrite /trace !map_assoc //=; first 3 by smt().
rewrite /gate /party_exec /=.
rewrite !map_assoc //=; first 2 by smt().
rewrite !map_assoc //=; first by smt().
rewrite -!map_comp /(\o) /=.
congr.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.

case (x0 \in cr{2}); progress.
rewrite map_assoc //=.
smt().
rewrite /share /=.
congr.
rewrite !map_assoc; first by smt().
move : (H0 x0); rewrite H9 /=.
rewrite H10 /=.
progress.

        have : exists inp, Some inp = assoc xs{2} x0.
          exists (oget (assoc xs{2} x0)).
          by rewrite -Core.some_oget; first by rewrite assocTP => /#.
        progress; move : H12; progress.
        have ->: oget (assoc xs{2} x0) = inp by smt().
        clear H12.
        elim inp => pub sec /=.
        elim sec => sec1 sec2; progress.
rewrite map_assoc; first by smt().
simplify.
rewrite (H11 pid (fmul sec1 sec2) (fmul fzero fzero)).
smt.
done.

       rewrite /simulator /= /gate /eval /party_exec1 /party_exec2 /= /input /= /output /get_messages_to /=.

rewrite -eq_in_map => pid; progress.
rewrite /trace !map_assoc //=.
move : (H0 pid); rewrite H8 /=.
have ->: pid \in pid_set by smt().
smt().
rewrite /trace !map_assoc //=; first 3 by smt().
rewrite !map_assoc //=; first by smt().
rewrite -!map_comp /(\o) /=.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.
case (x0 \in cr{2}); progress.
rewrite map_assoc //=.
smt().
rewrite /share /=.
congr.
rewrite !map_assoc; first by smt().
move : (H0 x0); rewrite H9 /=.
rewrite H10 /=.
progress.

        have : exists inp, Some inp = assoc xs{2} x0.
          exists (oget (assoc xs{2} x0)).
          by rewrite -Core.some_oget; first by rewrite assocTP => /#.
        progress.
        have ->: oget (assoc xs{2} x0) = inp by smt().
        clear H12.
        elim inp => pub sec /=.
        elim sec => sec1 sec2; progress.
rewrite map_assoc; first by smt().
simplify.
rewrite (H11 pid (fmul sec1 sec2) (fmul fzero fzero)).
smt.
done.
    qed.

    lemma security &m aux cr :
      Pr [ GameReal(D,R).main(aux,cr) @ &m : res ] - Pr [ GameIdeal(D,R).main(aux,cr) @ &m : res ] = 0%r.
    proof. 
      progress.
      have ?: Pr [ GameReal(D,R).main(aux,cr) @ &m : res ] = Pr [ GameIdeal(D,R).main(aux,cr) @ &m : res ] by byequiv real_ideal_equiv. 
      by smt().
    qed.

  end section Security.

end BGWMultiplication.
