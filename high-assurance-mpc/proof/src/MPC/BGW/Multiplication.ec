require import Int IntDiv List Distr DList Real.

from General require import PrimeField ListExt FieldPolynomial.
from ArithmeticProtocol require import MultiplicationGate.
from Functionalities require import MultiplicationFunctionality.
from MPC require import GatePrivacy.
from SecretSharing require import Shamir.

theory BGWMultiplication.

  const n : {int | 2 <= n} as n_pos.
  const t : {int | if n %% 2 = 0 then 0 <= t < n%/2 else 0 <= t <= n%/2} as t_pos.

  clone import Shamir with op n = n, op t = t.

  clone import MultiplicationFunctionality with theory SecretSharingScheme <- Shamir.

  type rand_t = polynomial.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand (r : rand_t) : bool = Shamir.valid_rand r.
  op valid_rands (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ all (fun r => valid_rand (snd r)) rs.

  type output_t = share_t.
  type outputs_t = (pid_t * share_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  type msgs_t = t.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to (pid : pid_t) (ms : out_messages_t) : msgs_t = odflt witness (assoc ms pid).
  op get_messages_from (pid : pid_t) (ms : in_messages_t) : msgs_t = odflt witness (assoc ms pid).

  type trace_t = in_messages_t.
  type traces_t = (pid_t * in_messages_t) list.
  op trace (pid : pid_t) (tr : traces_t) : in_messages_t = odflt [] (assoc tr pid).
  
  type view_t = input_t * rand_t * in_messages_t.

  op party_exec1 (r : rand_t) (x : input_t) : (pid_t * share_t) list = 
    let (pub, sec) = x in
    let (sec1, sec2) = sec in Shamir.share r (fmul sec1 sec2).

  op party_exec2 (ms : (pid_t * share_t) list) : output_t = 
    interpolate fzero ms.

  op out_messages (pid : pid_t) (v : view_t) : out_messages_t = 
    let (x, r, tr) = v in party_exec1 r x.

  op local_output (pid : pid_t) (v : view_t) : output_t = 
    let (x, r, tr) = v in party_exec2 tr.

  op gate (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let p1s = map (fun pid => (pid, party_exec1 (oget (assoc rs pid)) (oget (assoc xs pid)))) pid_set in
    let ms = map (fun pid => (pid, map (fun ms => let (sender, m) = ms in (sender, get_messages_to pid m)) p1s)) pid_set in 
    let p2s = map (fun pid => (pid, party_exec2 (oget (assoc ms pid)))) pid_set in
    (ms, p2s).

  clone import MultiplicationGate with
    theory SecretSharingScheme <- Shamir,
    type rand_t = rand_t,
    op valid_rand = valid_rand,
    type msgs_t = msgs_t,
    op get_messages_to = get_messages_to,
    op get_messages_from = get_messages_from,
    op out_messages = out_messages,
    op local_output = local_output,
    op gate = gate
  proof *.
  realize Gate.correct.
    rewrite /valid_input /valid_inputs /valid_rands /valid_rand /valid_secret /sinput /input /output_pred /gate /f /party_exec1 /party_exec2 /Shamir.pid_set /reconstruct /sinput /input; progress.
    move : H9; rewrite allP; progress.
    move : H3 H7; rewrite /share /=; progress.
    rewrite -H3 -H7.
    have ->: (map (fun (pid1 : pid_t) => (pid1, let (_, sec) = oget (assoc xs pid1) in let (sec1, sec2) = sec in (share (oget (assoc rs pid1)) (fmul sec1 sec2))%Shamir)) pid_set) = (map (fun (pid1 : pid_t) => (pid1, (share (oget (assoc rs pid1)) (fmul (eval pid1 (update r 0 s)) (eval pid1 (update r' 0 s')))))) pid_set).
      rewrite -(eq_in_map) => x hx /=.
      move : H3 H7.
      rewrite /share /= -!eq_in_map /sinput /MultiplicationFunctionality.input; progress.
      rewrite H3 // H7 //=. 
      have : exists pub sec, (pub, sec) = oget (assoc xs x)
        by exists (oget (assoc xs x)).`1 (oget (assoc xs x)).`2 => /#.
      progress; rewrite -H10 /=; move : H10.
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
        by rewrite -eq_in_map; progress; rewrite map_assoc.
    rewrite /interpolate /=.
    have ->: (interpolate_loop fzero (unzip1 (map (fun (pid : pid_t) => (pid, sumt (interpolate_loop fzero (unzip1 (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set)) (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set)))) pid_set)) (map (fun (pid : pid_t) => (pid, foldr (fun (x y : t) => fadd x y) fzero (interpolate_loop fzero (unzip1 (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set)) (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set)))) pid_set)) = (interpolate_loop fzero pid_set (map (fun (pid : pid_t) => (pid, sumt (interpolate_loop fzero pid_set (map (fun (x : pid_t) => (x, eval pid (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set)))) pid_set)).
      rewrite !unzip1_map_assoc /=; do 2! congr.
      by rewrite fun_ext /(==); progress; rewrite !unzip1_map_assoc /=.
    have ->: sumt (interpolate_loop fzero (unzip1 (map (fun (pid : coeficient) => (pid, eval pid (update r 0 s))) pid_set)) (map (fun (pid : coeficient) => (pid, eval pid (update r 0 s))) pid_set)) = (sumt (interpolate_loop fzero pid_set (map (fun (pid : coeficient) => (pid, eval pid (update r 0 s))) pid_set))).
      by do 2! congr; rewrite !unzip1_map_assoc /=.
    have ->: (sumt (interpolate_loop fzero (unzip1 (map (fun (pid : coeficient) => (pid, eval pid (update r' 0 s'))) pid_set)) (map (fun (pid : coeficient) => (pid, eval pid (update r' 0 s'))) pid_set))) = (sumt (interpolate_loop fzero pid_set (map (fun (pid : coeficient) => (pid, eval pid (update r' 0 s'))) pid_set))).
      by do 2! congr; rewrite !unzip1_map_assoc /=.
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
        have H11 : unzip1 rs = pid_set by done.
        move : (H9 (x,(oget (assoc rs x)))).
        have ->: (x, oget (assoc rs x)) \in rs by rewrite assoc_get_mem => /#.
        by simplify; progress; rewrite H12 /t /n; smt(t_pos).
    have ->: (map (fun (x : pid_t) => (x, eval fzero (update (oget (assoc rs x)) 0 (fmul (eval x (update r 0 s)) (eval x (update r' 0 s')))))) pid_set) = (map (fun (x : pid_t) => (x, eval x (mul (update r 0 s) (update r' 0 s')) )) pid_set).
      rewrite -eq_in_map; progress; rewrite eval_update0.
      have H11 : unzip1 rs = pid_set by done.
      move : (H9 (x,(oget (assoc rs x)))).
      have ->: (x, oget (assoc rs x)) \in rs by rewrite assoc_get_mem => /#.
      progress; rewrite expo_diff_count //; first 2 by rewrite H13 /t; smt(t_pos).
      by rewrite eval_mul.
    rewrite interpolate_eval; first by apply pid_set_uniq.
      by rewrite degree_mul !degree_update0 H0 H4 /t /n pid_set_size; smt.
    have ->: (sumt (map (fun (x : coeficient) => fmul (basis fzero x pid_set) (eval x (update r 0 s))) pid_set)) = interpolate fzero (map (fun x => (x, eval x (update r 0 s))) pid_set).
      rewrite /interpolate /interpolate_loop /= -map_comp /(\o) /=; congr.
      by rewrite -eq_in_map; progress; rewrite unzip1_map_assoc.
    have ->: (sumt (map (fun (x : coeficient) => fmul (basis fzero x pid_set) (eval x (update r' 0 s'))) pid_set)) = interpolate fzero (map (fun x => (x, eval x (update r' 0 s'))) pid_set).
      rewrite /interpolate /interpolate_loop /= -map_comp /(\o) /=; congr.
      by rewrite -eq_in_map; progress; rewrite unzip1_map_assoc.
    rewrite interpolate_eval; first by apply pid_set_uniq.
      by rewrite degree_update0 pid_set_size H0 /n /t; smt(t_pos).
    rewrite interpolate_eval; first by apply pid_set_uniq.
      by rewrite degree_update0 pid_set_size H4 /n /t; smt(t_pos).
    by rewrite eval_mul.
  qed.
  realize Gate.local_output_correct.
    by rewrite /local_output /output /gate /party_exec1 /party_exec2 /input 
            /pid_set /BGWMultiplication.get_messages_to => />; progress; rewrite map_assoc //=.
  qed.
  realize Gate.messages_consistency.
    rewrite /local_output /output /gate /party_exec1 /party_exec2 /input 
            /pid_set /get_messages_to /out_messages /trace /party_exec1 => />; progress. 
    by rewrite /get_messages_from !map_assoc /share //= -map_comp /(\o) /= map_assoc //.
  qed.

  op simulator (rs : rands_t) (xs : inputs_t) (cr : pid_t list) : view_t list =
    let pub = fst (oget (assoc xs (head witness cr))) in
    let xs' = map (fun pid => (pid, if pid \in cr then oget (assoc xs pid) else (pub, (fzero, fzero)))) pid_set in
    let p1s = map (fun pid => (pid, party_exec1 (oget (assoc rs pid)) (oget (assoc xs' pid)))) pid_set in
    let ms = map (fun pid => (pid, map (fun ms => let (sender, m) = ms in (sender, get_messages_to pid m)) p1s)) pid_set in
    (map (fun pid => (oget (assoc xs pid), oget (assoc rs pid), oget (assoc ms pid))) cr).

  clone import Privacy with 
    theory Gate <- MultiplicationGate.Gate,
    op simulator = simulator.

  section Security.

    declare module D : Distinguisher_t{RealEvaluator,IdealEvaluator}.

    module R : Rand_t = {
      proc gen(xs : inputs_t, cr : pid_t list) : rands_t = {
        var ps, i, p, pid;
        i <- 0; ps <- [];
        while (i < n) {
          pid <- nth witness pid_set i;
          p <@ PolynomialRand.gen(t);
          ps <- ps ++ [(pid,p)];
          i <- i + 1;
        }
        return ps;
      }
    }.

    module SR : Rand_t = {
      proc gen(xs : inputs_t, cr : pid_t list) : rands_t = {
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
      equiv [ R.gen ~ SR.gen : cr_ = cr{2} /\ (forall pid, pid \in cr{2} => pid \in pid_set) ==> 
                 unzip1 res{1} = pid_set /\ unzip1 res{1} = unzip1 res{2} /\
                 (forall pid, pid \in pid_set => 
                   if pid \in cr_ then oget (assoc res{1} pid) = oget (assoc res{2} pid)
                   else  (forall x c c', x <> fzero => eval x (update (oget (assoc res{1} pid)) 0 c) = eval x (update (oget (assoc res{2} pid)) 0 c'))) /\
                 (forall pid, pid \in pid_set => oget (assoc res{1} pid) \in dpolynomial t) /\
                 (forall pid, pid \in pid_set => oget (assoc res{2} pid) \in dpolynomial t) ].
    proof.
      proc; sp.
      while (={i} /\ 0 <= i{1} <= n /\ (forall pid, pid \in cr{2} => pid \in pid_set) /\
            (unzip1 ps{1} = take i{1} pid_set) /\ cr_ = cr{2} /\ unzip1 ps{1} = unzip1 ps{2} /\
            (forall pid, pid \in unzip1 ps{1} => if pid \in cr_ then 
                                                   oget (assoc ps{1} pid) = oget (assoc ps{2} pid)
                                                else (forall x c c', x <> fzero => eval x (update (oget (assoc ps{1} pid)) 0 c) = eval x (update (oget (assoc ps{2} pid)) 0 c'))) /\
            (forall pid, pid \in unzip1 ps{1} => oget (assoc ps{1} pid) \in dpolynomial t) /\
            (forall pid, pid \in unzip1 ps{2} => oget (assoc ps{2} pid) \in dpolynomial t)).
        wp; sp; if{2}.
          inline PolynomialRand.gen.
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
      GameReal(D,R).main ~ GameIdeal(D,SR).main :
      ={glob D, xs, cr} /\ valid_inputs xs{1} /\ size cr{1} = t /\ (forall pid, pid \in cr{1} => pid \in pid_set) ==> ={res}.
    proof.
      proc. 
      seq 1 1 : (#pre /\ 
                 (forall pid, pid \in pid_set => 
                   if pid \in cr{2} then oget (assoc r{1} pid) = oget (assoc r{2} pid)
                   else  (forall x c c', x <> fzero => eval x (update (oget (assoc r{1} pid)) 0 c) = eval x (update (oget (assoc r{2} pid)) 0 c'))) /\
                 unzip1 r{1} = pid_set /\ unzip1 r{1} = unzip1 r{2} /\
                 (forall pid, pid \in pid_set => oget (assoc r{1} pid) \in dpolynomial t) /\
                 (forall pid, pid \in pid_set => oget (assoc r{2} pid) \in dpolynomial t)).
        exists* cr{2}; elim* => cr.
        by call (rand_srand_equiv cr).
      if; last by rnd.
        progress.
          by rewrite -H4 H3 /MultiplicationGate.Gate.GateFunctionality.pid_set /Shamir.pid_set.
          rewrite allP /valid_rand; progress.
            rewrite /BGWMultiplication.Shamir.t (dpolynomial_degree x.`2 BGWMultiplication.t) //.
              by smt(t_pos).
              move : (H6 x.`1).
              have ->: x.`1 \in pid_set by rewrite -H3 H4 mapP; exists x => /#.
              simplify; move : (mem_assoc_uniq r{2} x.`1 x.`2).
              have ->: uniq (unzip1 r{2}) by rewrite -H4 H3 pid_set_uniq.
              by simplify => /#.
            rewrite /BGWMultiplication.Shamir.t (dpolynomial_size x.`2 BGWMultiplication.t) //.
              by smt(t_pos).
              move : (H6 x.`1).
              have ->: x.`1 \in pid_set by rewrite -H3 H4 mapP; exists x => /#.
              simplify; move : (mem_assoc_uniq r{2} x.`1 x.`2).
              have ->: uniq (unzip1 r{2}) by rewrite -H4 H3 pid_set_uniq.
              by simplify => /#.
            rewrite /BGWMultiplication.Shamir.t (dpolynomial_exp x.`2 BGWMultiplication.t) //.
              by smt(t_pos).
              move : (H6 x.`1).
              have ->: x.`1 \in pid_set by rewrite -H3 H4 mapP; exists x => /#.
              simplify; move : (mem_assoc_uniq r{2} x.`1 x.`2).
              have ->: uniq (unzip1 r{2}) by rewrite -H4 H3 pid_set_uniq.
              by simplify => /#.
          by rewrite H3 /MultiplicationGate.Gate.GateFunctionality.pid_set /Shamir.pid_set.
          rewrite allP /valid_rand; progress.
            rewrite /BGWMultiplication.Shamir.t (dpolynomial_degree x.`2 BGWMultiplication.t) //.
              by smt(t_pos).
              move : (H5 x.`1).
              have ->: x.`1 \in pid_set by rewrite -H3 mapP; exists x => /#.
              simplify; move : (mem_assoc_uniq r{1} x.`1 x.`2).
              have ->: uniq (unzip1 r{1}) by rewrite H3 pid_set_uniq.
              by simplify => /#.
            rewrite /BGWMultiplication.Shamir.t (dpolynomial_size x.`2 BGWMultiplication.t) //.
              by smt(t_pos).
              move : (H5 x.`1).
              have ->: x.`1 \in pid_set by rewrite -H3 mapP; exists x => /#.
              simplify; move : (mem_assoc_uniq r{1} x.`1 x.`2).
              have ->: uniq (unzip1 r{1}) by rewrite H3 pid_set_uniq.
              by simplify => /#.
            rewrite /BGWMultiplication.Shamir.t (dpolynomial_exp x.`2 BGWMultiplication.t) //.
              by smt(t_pos).
              move : (H5 x.`1).
              have ->: x.`1 \in pid_set by rewrite -H3 mapP; exists x => /#.
              simplify; move : (mem_assoc_uniq r{1} x.`1 x.`2).
              have ->: uniq (unzip1 r{1}) by rewrite H3 pid_set_uniq.
              by simplify => /#.
      inline *; call (_ : true); wp; skip; progress.
      rewrite (eq_from_nth (witness, witness, witness) (zip3 ((MultiplicationGate.Gate.extract_inputs xs{2} cr{2})) ((MultiplicationGate.Gate.extract_rands r{1} cr{2})) ((MultiplicationGate.Gate.extract_traces ((MultiplicationGate.Gate.gate r{1} xs{2})).`1 cr{2}))) ((Privacy.simulator r{2} xs{2} cr{2}))) //.
        by rewrite size_zip3 /= /simulator /= !size_map => /#.
        rewrite size_zip3 /= !size_map.
        have ->: min (min (size cr{2}) (size cr{2})) (size cr{2}) = size cr{2} by smt().
        move => pid; progress.
        rewrite nth_zip3; first 2 by rewrite !size_map.
        rewrite /extract_inputs (nth_map fzero) // /input /=.
        rewrite /extract_rands (nth_map fzero) // /rand /=.
        rewrite /extract_traces (nth_map fzero) // /trace /=.
        rewrite /simulator /= (nth_map fzero (witness, witness, witness)) //=.
        split.
          move : (H2 (nth fzero cr{2} pid)).
          have H10 : nth fzero cr{2} pid \in pid_set by smt(mem_nth).
          rewrite H10 /=; have ->: nth fzero cr{2} pid \in cr{2} by smt(mem_nth).
          by done. 
        rewrite /gate /= !map_assoc /=; first 2 by smt(mem_nth).
        rewrite -!map_comp /(\o) /= -eq_in_map; progress.
        rewrite map_assoc //=; case (x \in cr{2}); progress.
          move : (H2 x).
          rewrite H10 H11 /=; progress.
          by rewrite H12.
        rewrite /get_messages_to /party_exec1; congr; congr => /=.
        rewrite /share /=.
        have : exists inp, Some inp = assoc xs{2} x.
          exists (oget (assoc xs{2} x)).
          by rewrite -Core.some_oget; first by rewrite assocTP => /#.
        progress; move : H12.
        elim inp => pub sec /=.
        elim sec => sec1 sec2; progress.
        rewrite -H12 /= -eq_in_map; progress.
        move : (H2 x).
        rewrite H10 H11 /=; progress.
        by rewrite (H14 x0 (fmul sec1 sec2) (fmul fzero fzero)); first by rewrite (pid_set_neq0).
    qed.

    lemma security &m xs cr :
      valid_inputs xs =>
      size cr = t => 
      (forall pid, pid \in cr => pid \in pid_set) =>
      Pr [ GameReal(D,R).main(xs,cr) @ &m : res ] - Pr [ GameIdeal(D,SR).main(xs,cr) @ &m : res ] = 0%r.
    proof. 
      progress.
      have ?: Pr [ GameReal(D,R).main(xs,cr) @ &m : res ] = Pr [ GameIdeal(D,SR).main(xs,cr) @ &m : res ] by byequiv real_ideal_equiv. 
      by smt().
    qed.

  end section Security.

end BGWMultiplication.
