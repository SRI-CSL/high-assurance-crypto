require import AllCore List.

from General require import ListExt.
from ArithmeticProtocol require import ArithmeticProtocol.
from MPC require import AProtocol AGate ProtocolWeak ProtocolPrivacy GatePrivacy.
from Circuit require import ACircuit ArithmeticCircuit.
from SecretSharing require import ASecretSharingScheme.

theory WeakPrivacyComposition.

  clone import ArithmeticProtocol.
  import ArithP.
  import SecretSharingScheme.
  import ArithmeticProtocolFunctionality.

  clone import Gate as SG with
    op GateFunctionality.n = ProtocolFunctionality.n,
    op GateFunctionality.t = ProtocolFunctionality.t,
    type GateFunctionality.pid_t = ProtocolFunctionality.pid_t,
    op GateFunctionality.pid_set = ProtocolFunctionality.pid_set,
    type GateFunctionality.pinput_t = unit,
    type GateFunctionality.sinput_t = share_t,
    type GateFunctionality.output_t = secret_t,
    type poutput_t = share_t,
    op GateFunctionality.f (x : inputs_t) =
      let ys = map (fun pid => (pid, (sinput pid x).`1)) pid_set in
      let y = reconstruct ys in 
      map (fun pid => (pid, y)) pid_set,
    op GateFunctionality.valid_inputs xs =
      unzip1 xs = pid_set /\
      let sec = map (fun pid => (pid, (sinput pid xs).`1)) pid_set in
      (exists r s, valid_secret s /\ SecretSharingScheme.valid_rand r /\ share r s = sec).

  lemma good_refresh s : 
    (forall xs xs', 
      reconstruct (map (fun pid => (pid, (SG.GateFunctionality.sinput pid xs).`1)) SecretSharingScheme.pid_set) = s => 
      reconstruct (map (fun pid => (pid, (SG.GateFunctionality.sinput pid xs').`1)) SecretSharingScheme.pid_set) = s =>
        let fss = SG.GateFunctionality.f xs in
        let fss' = SG.GateFunctionality.f xs' in
        fss = fss' /\ unzip1 fss = SecretSharingScheme.pid_set /\  (exists b, all (fun x => snd x = b) fss)).
  proof.
progress.
rewrite /f /input.
simplify.
move : H.
rewrite /sinput /input.
progress.
rewrite H.
rewrite /pid_set.
done.
rewrite /f /=.
by rewrite -map_comp /(\o) /= map_id /=.
exists (reconstruct (map (fun (pid : GateFunctionality.pid_t) => (pid, (GateFunctionality.sinput pid xs).`1)) SecretSharingScheme.pid_set)).
rewrite allP /f /=.
move => x.
rewrite mapP.
done.
qed.

  axiom strong_valid_inputs_from_weak topo gg rs xs : 
    unzip1 xs = SecretSharingScheme.pid_set =>
    ProtocolFunctionality.valid_inputs_topology topo xs =>
    let ys = (eval_circuit gg rs xs).`2 in
    SG.GateFunctionality.valid_inputs (map (fun pid => (pid, ((), (oget (assoc ys pid), witness)))) ProtocolFunctionality.pid_set).

  clone import Protocol as PP with
    type ProtocolFunctionality.Circuit.Domain.wire_t = ArithP.ProtocolFunctionality.Circuit.Domain.wire_t,
    op ProtocolFunctionality.Circuit.Domain.wire_to_bool = ArithP.ProtocolFunctionality.Circuit.Domain.wire_to_bool,

    type ProtocolFunctionality.Circuit.gates_t = ArithP.ProtocolFunctionality.Circuit.gates_t,
    op ProtocolFunctionality.Circuit.valid_gates = ArithP.ProtocolFunctionality.Circuit.valid_gates,

    op ProtocolFunctionality.n = ArithP.ProtocolFunctionality.n,
    op ProtocolFunctionality.t = ArithP.ProtocolFunctionality.t,
    type ProtocolFunctionality.pid_t = ArithP.ProtocolFunctionality.pid_t,
    op ProtocolFunctionality.pid_set = ArithP.ProtocolFunctionality.pid_set,
    type ProtocolFunctionality.pinput_t = ArithP.ProtocolFunctionality.pinput_t,
    type ProtocolFunctionality.sinput_t = ArithP.ProtocolFunctionality.sinput_t,
    op ProtocolFunctionality.valid_inputs = ArithP.ProtocolFunctionality.valid_inputs,
    type ProtocolFunctionality.output_t = ArithP.ProtocolFunctionality.output_t,
    op ProtocolFunctionality.f = ArithP.ProtocolFunctionality.f,

      (*let y = output (head witness pid_set) ys in
      let puby = public_encoding y in
      GateFunctionality.f (map (fun (pid : WP.ProtocolFunctionality.pid_t) => (pid, (tt, oget (assoc puby pid)))) pid_set),*)
      
(*      let ys = map (fun pid => (pid, y)) pid_set in ys.
      let xsp = map (fun pid => (pid, ((), WP.output pid y))) pid_set in
      SG.GateFunctionality.f xsp,*)

    type rand_t = ArithP.rand_t * SG.rand_t,
    op valid_rand c r =
      let (topo, gg) = c in
      let (rwp, rsp) = r in
      ArithP.valid_rand c rwp /\ SG.valid_rand rsp,
    type msgs_t = ArithP.msgs_t * SG.msgs_t,
    type in_messages_t = gate_local_traces_t * SG.in_messages_t,
    type out_messages_t = ArithP.out_messages_t * SG.out_messages_t,
    op get_messages_from pid im =
      let (imwp, imsp) = im in (get_local_msgs_from pid imwp, SG.get_messages_from pid imsp),
    op get_messages_to pid om =
      let (omwp, omsp) = om in (ArithP.get_messages_to pid omwp, SG.get_messages_to pid omsp),

    type poutput_t = share_t,

    op protocol (c : ProtocolFunctionality.Circuit.circuit_t) (rs : rands_t) (xs : ProtocolFunctionality.inputs_t) = 
      let (topo, gg) = c in
      let rwp = map (fun pid => (pid, fst (rand pid rs))) ProtocolFunctionality.pid_set in
      let (trwp, ys) = eval_circuit gg rwp xs in
      let rsp = map (fun pid => (pid, snd (rand pid rs))) ProtocolFunctionality.pid_set in
      let xsp = map (fun pid => (pid, ((), (oget (assoc ys pid), witness)))) ProtocolFunctionality.pid_set in
      let (trsp, zs) = SG.gate rsp xsp in
      (map (fun pid => (pid, ((trace pid trsp).`1, (get_local_trace pid trwp, (trace pid trsp).`2)))) ProtocolFunctionality.pid_set, zs),
     
    op local_output c pid v = 
      let (x, r, tr) = v in
      let (topo, gg) = c in
      let (riwp, risp) = r in
      let (ys, ims) = tr in
      let (imswp, imssp) = ims in
      let yi = local_output_gates pid x riwp imswp in
      let zi = SG.local_output pid (((),(yi, witness)), risp, (ys, imssp)) in
      zi,

    op out_messages c pid v = 
      let (topo, gg) = c in
      let (xi, ri, tri) = v in
      let (riwp, risp) = ri in
      let (ys, ims) = tri in
      let (triwp, trisp) = ims in
      let yi = local_output_gates pid xi riwp triwp in
      let imwp = out_messages_gates pid xi riwp triwp in
      let imsp = SG.out_messages pid (((),(yi, witness<:share_t>)), risp, (ys, trisp)) in
      (imwp, imsp)
    proof *.
    realize ProtocolFunctionality.n_pos by apply n_pos.
    realize ProtocolFunctionality.t_pos by apply t_pos.
    realize ProtocolFunctionality.pid_set_uniq by apply pid_set_uniq.
    realize ProtocolFunctionality.pid_set_size by apply pid_set_size.
    realize correct.
      rewrite /valid_inputs /valid_input /valid_rands /valid_rand /protocol /f /=
              /pinput /sinput /input /output /trace /= => c rs xs => /> H H0; move : H.
      elim c => topo gg /=; progress.
      have : exists (trwp, ys), (trwp, ys) = eval_circuit gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs
        by exists (eval_circuit gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs).`1
                  (eval_circuit gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs).`2 => /#.
      progress; rewrite -H4 /=.
      have : exists (trsp, zs), (trsp, zs) = gate (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (tt, (oget (assoc ys pid), witness)))) ProtocolFunctionality.pid_set)
        by exists (gate (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (tt, (oget (assoc ys pid), witness)))) ProtocolFunctionality.pid_set)).`1
                  (gate (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (tt, (oget (assoc ys pid), witness)))) ProtocolFunctionality.pid_set)).`2 => /#.
      progress; rewrite -H5 /=.
      pose grs := (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set).
      pose gxs := (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (tt, oget (assoc ys pid)))) ProtocolFunctionality.pid_set).
      move : H1 H; elim topo => np ns m q /=; progress.
      rewrite eq_assoc_map 1:smt. 
      have ->: (unzip1 zs) = pid_set by smt.
      rewrite -eq_in_map => pid; progress. 
      rewrite /eval_circuit.
move : (correct_eval_gates (np,ns,m,q) gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs ((oget (assoc xs (head witness SecretSharingScheme.pid_set))).`1, map SecretSharingScheme.reconstruct
     (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc xs pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite H.
have ->: (ArithmeticCircuit.Circuit.valid_topology (np, ns, m, q)) by smt().
have ->: (ArithmeticCircuit.valid_gates ((np, ns, m, q), gg)) by smt().
have ->: all
   (fun (pid0 : pid_t) =>
      gates_valid_rand gg
        (oget
           (assoc
              (map (fun (pid1 : ProtocolFunctionality.pid_t) => (pid1, (rand pid1 rs).`1))
                 ProtocolFunctionality.pid_set) pid0))) pid_set.
rewrite allP; progress.
rewrite !map_assoc //=.
by move : (H3 x); rewrite H7 => /#.
have ->: pinput_finput_valid
   (((np, ns, m, q), witness), xs,
    ((oget (assoc xs (head witness SecretSharingScheme.pid_set))).`1,
     map SecretSharingScheme.reconstruct
       (map
          (fun (k : int) =>
             map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc xs pid0)).`2 k))
               SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite /pinput_finput_valid /=.
rewrite !size_map.
move : H.
rewrite /valid_inputs_topology /= /pinput /sinput /input /=.
progress.
by rewrite H; first by smt(pid_set_size n_pos).
by rewrite size_range /max => /#.
by rewrite H. 
by rewrite H7.
rewrite !map_assoc //= /pinput /input /=.
move : (H9 k); rewrite H11 H12 /=.
progress.
move : H14; rewrite allP; progress.
have : (pid0, nth witness (oget (assoc xs pid0)).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc xs pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
by exists pid0 => /=.
have : ((head witness SecretSharingScheme.pid_set), nth witness (oget (assoc xs (head witness SecretSharingScheme.pid_set))).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc xs pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
exists (head witness SecretSharingScheme.pid_set) => /=.
smt(pid_set_size n_pos).
smt().

rewrite -!map_comp /(\o) /=.
rewrite (nth_map witness).
by rewrite size_range => /#.
simplify.
rewrite /reconstruct.
congr.
rewrite -eq_in_map => pid'; progress.
rewrite nth_range 1:/#.
simplify.
rewrite /input.
done.

rewrite /pgates_fgates_valid /=.
progress.
rewrite -H8.

      move : (SG.correct (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (tt, (oget (assoc ys pid), witness)))) ProtocolFunctionality.pid_set)).
      have ->: (GateFunctionality.valid_inputs (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (tt, (oget (assoc ys pid0), witness)))) ProtocolFunctionality.pid_set)).
        move : (strong_valid_inputs_from_weak (np,ns,m,q) gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) pid_set) xs).
        have ->: unzip1 xs = SecretSharingScheme.pid_set by smt.
        have ->: (ArithmeticProtocolFunctionality.ProtocolFunctionality.valid_inputs_topology (np, ns, m, q) xs) by smt(). 
        simplify.
        have ->: (eval_circuit gg (map (fun (pid1 : ProtocolFunctionality.pid_t) => (pid1, (rand pid1 rs).`1)) pid_set) xs).`2 = ys by smt().
        by smt().
      simplify.
      rewrite /valid_rands /= -!map_comp /(\o) !map_id /= /pid_set /=.
      have ->: (forall (pid : GateFunctionality.pid_t), pid \in pid_set => valid_rand (oget (assoc (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (rand pid0 rs).`2)) pid_set) pid))) <=> true. 
        progress; move : (H3 pid0); rewrite H12 /=; progress.
        by rewrite map_assoc //= /rand; move : H13 => /#. 

rewrite /f /=.
rewrite /sinput /input.
have ->: map
  (fun (pid0 : SecretSharingScheme.pid_t) =>
     (pid0,
      reconstruct
        (map
           (fun (pid1 : GateFunctionality.pid_t) =>
              (pid1,
               (oget
                  (assoc
                     (map (fun (pid2 : ProtocolFunctionality.pid_t) => (pid2, (tt, (oget (assoc ys pid2), witness<:share_t>))))
                        pid_set) pid1)).`2.`1)) GateFunctionality.pid_set))) GateFunctionality.pid_set =
map
  (fun (pid0 : SecretSharingScheme.pid_t) =>
     (pid0,
      reconstruct ys)) GateFunctionality.pid_set.
rewrite -eq_in_map => pid'; progress.
have ->: (map
     (fun (pid1 : GateFunctionality.pid_t) =>
        (pid1,
         (oget
            (assoc
               (map (fun (pid2 : ProtocolFunctionality.pid_t) => (pid2, (tt, (oget (assoc ys pid2), witness<:share_t>)))) pid_set)
               pid1)).`2.`1)) GateFunctionality.pid_set) = 
(map
     (fun (pid1 : GateFunctionality.pid_t) =>
        (pid1, oget (assoc ys pid1)))
     GateFunctionality.pid_set).
rewrite -eq_in_map => pid''; progress.
by rewrite !map_assoc //=.

rewrite eq_assoc_map 1:smt.
congr.
have ->: (unzip1 ys) = pid_set by smt.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.
progress.
have ->: zs = (gate (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (rand pid0 rs).`2)) pid_set)
        (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (tt, (oget (assoc ys pid0), witness)))) pid_set)).`2 by smt().
rewrite H12.
rewrite !map_assoc //=.
smt().
    qed.
    realize local_output_correct.
      progress; move : x1 x2 H0 => tr ys; progress.
      rewrite /output /= /local_output /=.
      have ->: tr = (protocol c rs xs).`1 by smt().
      have ->: ys = (protocol c rs xs).`2 by smt().
      clear H0; elim c => topo gg /=.
      move : (local_output_correct_gates topo gg pid xs (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set)).
      rewrite H /= /input /rand /trace /output /= !map_assoc //=; progress.
      rewrite /protocol /= /eval_circuit.
      have : exists (trwp, ys), (trwp, ys) = eval_gates gg (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (rand pid0 rs).`1)) ProtocolFunctionality.pid_set) xs
        by exists (eval_gates gg (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (rand pid0 rs).`1)) ProtocolFunctionality.pid_set) xs).`1 (eval_gates gg (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (rand pid0 rs).`1)) ProtocolFunctionality.pid_set) xs).`2 => /#.
      move => H1; elim H1 => trwp ys'; progress.
      rewrite -H1 /=.
      have : exists (trsp, zs), (trsp, zs) = gate (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (rand pid0 rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys' pid0), witness)))) ProtocolFunctionality.pid_set) 
        by exists (gate (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (rand pid0 rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys' pid0), witness)))) ProtocolFunctionality.pid_set)).`1 (gate (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (rand pid0 rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys' pid0), witness)))) ProtocolFunctionality.pid_set)).`2 => /#.
      progress; rewrite -H2 /=.
      rewrite !map_assoc //=.
      move : (SG.local_output_correct pid (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc ys' pid), witness)))) pid_set) (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set)).
      rewrite H /= /input /rand /trace /output /= !map_assoc //= -H2 /=; progress.
      rewrite H3.
      have : exists (riwp, risp), (riwp, risp) = oget (assoc rs pid)
        by exists (oget (assoc rs pid)).`1 (oget (assoc rs pid)).`2 => /#.
      progress; rewrite -H4 /=.
      have ->: local_output_gates pid (oget (assoc xs pid)) riwp (get_local_trace pid trwp) = oget (assoc ys' pid). 
have ->: ys' = (eval_gates gg
      (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (rand pid0 rs).`1)) ProtocolFunctionality.pid_set) xs).`2 by smt().
rewrite H0.
by move : H1; rewrite /rand => /#.
move : H2; rewrite /gate /=.
smt().
qed.
    realize messages_consistency.
      progress; move : x1 x2 H1 => tr ys; progress.
      rewrite /get_messages_to /= /get_messages_from /out_messages /=.
      have ->: tr = (protocol c rs xs).`1 by smt().
      clear H1; elim c => topo gg /=.
      rewrite /protocol /eval_circuit /=.
      have : exists (trwp, ys), (trwp, ys) = eval_gates gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs
        by exists (eval_gates gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs).`1
                  (eval_gates gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs).`2 => /#.
      progress; rewrite -H1 /=.
      have : exists (trsp, zs), (trsp, zs) = gate (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (tt, (oget (assoc ys0 pid),witness)))) ProtocolFunctionality.pid_set)
        by exists (gate (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (tt, (oget (assoc ys0 pid),witness)))) ProtocolFunctionality.pid_set)).`1
                  (gate (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (tt, (oget (assoc ys0 pid),witness)))) ProtocolFunctionality.pid_set)).`2 => /#.
      progress; rewrite -H2 /=.
      rewrite /rand /trace /pinput /sinput /input !map_assoc //=.
      move : (local_output_correct_gates topo gg i xs (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set)).
      rewrite H /= /input /rand /trace /output /= !map_assoc //=; progress.
      have : exists (riwp, risp), (riwp, risp) = oget (assoc rs i) 
        by exists (oget (assoc rs i)).`1 (oget (assoc rs i)).`2 => /#.
      progress; rewrite -H4 /=.
      have ->: local_output_gates i (oget (assoc xs i)) riwp (get_local_trace i trwp) = oget (assoc ys0 i).
        have ->: riwp = (oget (assoc rs i)).`1 by smt().
        have ->: trwp = (eval_gates gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs).`1 by smt().
        have ->: ys0 = (eval_gates gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs).`2 by smt().
        by move : H3; rewrite /rand => /#. 
      move : (messages_gates_consistency gg i j xs (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set)).
      rewrite H H0 /= /input /rand /trace /output /= !map_assoc //= => H5.
      split.
        have ->: riwp = (oget (assoc rs i)).`1 by smt().
        have ->: trwp = (eval_gates gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs).`1 by smt(). 
        by done.
      move : (messages_consistency i j (map (fun (pid : pid_t) => (pid, ((), (oget (assoc ys0 pid),witness)))) ProtocolFunctionality.pid_set) (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set)).
      by rewrite H /= /input /rand /trace /output /= !map_assoc //= -H2 H0 /=; progress => /#.
    qed.
    realize global_consistency by admit.
    realize correct_domain.
      rewrite /valid_inputs /valid_input /valid_rands /valid_rand /protocol /eval_circuit /f /=
              /pinput /sinput /input /output /trace /= => c rs xs => />.
      elim c => topo gg => />.
      have : exists (trwp, ys), (trwp, ys) = eval_gates gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs
        by exists (eval_gates gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs).`1
                  (eval_gates gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs).`2 => /#.
      move => H3; elim H3 => trwp ys H3; rewrite -H3 /=.
      have : exists (trsp, zs), (trsp, zs) = gate (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc ys pid),witness)))) ProtocolFunctionality.pid_set)
        by exists (gate (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc ys pid),witness)))) ProtocolFunctionality.pid_set)).`1
                  (gate (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc ys pid),witness)))) ProtocolFunctionality.pid_set)).`2 => /#.
      move => H4; elim H4 => trsp zs H4; rewrite -H4 /=.
      have ->: zs = (gate (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc ys pid),witness)))) ProtocolFunctionality.pid_set)).`2 by smt().
      have ->: ys = (eval_gates gg (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`1)) ProtocolFunctionality.pid_set) xs).`2 by smt().
      rewrite -!map_comp /(\o) /= map_id /=.
      move : (SG.correct_domain (map (fun (pid : ProtocolFunctionality.pid_t) => (pid, (rand pid rs).`2)) ProtocolFunctionality.pid_set) (map (fun (pid : pid_t) => (pid, ((), (oget (assoc ys pid),witness))))
         ProtocolFunctionality.pid_set)).
      progress.
      have ->: (map
        (fun (pid : pid_t) =>
           (pid,
            (tt,
             (oget
               (assoc
                  (eval_gates gg
                     (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (rand pid0 rs).`1)) pid_set) xs).`2 pid),witness<:share_t>))))
        pid_set) = 
(map
        (fun (pid : pid_t) =>
           (pid,
            (tt,
             (oget
               (assoc
                  ys pid), witness))))
        pid_set).
rewrite -eq_in_map => pid; progress.
smt().
smt().
    qed.

  type aux_t.

  clone import ProtocolWeak.WeakSecurity as WP_S with 
    theory Protocol <- ArithP, type aux_t = aux_t.
  clone import GatePrivacy.Privacy as SP_S with 
    theory Gate <- SG, 
    type aux_t = WP_S.aux_t * ProtocolFunctionality.Circuit.circuit_t, 
    type env_input_t = env_input_t.
  clone import ProtocolPrivacy.Privacy with 
    theory Protocol <- PP, type aux_t =  WP_S.aux_t, type env_input_t = env_input_t.

  section Proof.

    module RealEvaluator1 = {
      proc eval(c : ProtocolFunctionality.Circuit.circuit_t, xs : PP.ProtocolFunctionality.inputs_t, cr : PP.ProtocolFunctionality.pid_t list, rs : rands_t) : views_t = {
        var vsc, rwp, trwp, ys;
        var rsp, xsp, xspc, vsp, ysf, ysfc;

        rwp <- map (fun pid => (pid, fst (rand pid rs))) ProtocolFunctionality.pid_set;
        (trwp, ys) <- eval_gates (snd c) rwp xs;
        rsp <- map (fun pid => (pid, snd (rand pid rs))) ProtocolFunctionality.pid_set;
        xsp <- map (fun pid => (pid, ((), (oget (assoc ys pid), witness)))) pid_set;
        xspc <- map (fun pid => (pid, SG.GateFunctionality.input pid xsp)) cr;

        ysf <- SG.GateFunctionality.f xsp;
        ysfc <- map (fun pid => (pid, SG.GateFunctionality.output pid ysf)) cr;
        vsp <- SP_S.simulator rsp xspc cr ysfc;

        vsc <- map (fun pid => (pid, (PP.ProtocolFunctionality.input pid xs, 
                                      ((rand pid rs).`1, (oget (assoc vsp pid)).`2), 
                                      ((oget (assoc vsp pid)).`3.`1,
                                      (get_local_trace pid trwp, (oget (assoc vsp pid)).`3.`2))))) cr;

        return vsc;
      }
    }.

    module D_SP (D : Privacy.Distinguisher_t) (R : WP_S.Rand_t) = {

      var trwp : gate_traces_t
      var xs : ProtocolFunctionality.inputs_t
      var cr : SG.GateFunctionality.pid_t list
      var rwp : ArithP.rands_t
      var xsp : SG.GateFunctionality.inputs_t

      proc choose(x : env_input_t, aux : SP_S.aux_t) : SG.GateFunctionality.inputs_t * SG.GateFunctionality.pid_t list = {

        var ys, aux', c;

        (aux',c) <- aux;
        (xs,cr) <@ D.choose(c, x, aux');
        rwp <@ R.gen(c, cr, aux');
        xsp <- [];
        if (ProtocolFunctionality.valid_inputs c xs /\ ArithP.valid_rands c rwp /\ WP_S.valid_corrupted_set cr) {
          (trwp, ys) <- eval_gates (snd c) rwp xs;
          xsp <- map (fun pid => (pid, ((), (oget (assoc ys pid), witness)))) ProtocolFunctionality.pid_set;
        }

        return (xsp,cr);
      }

      proc guess(vsc : SG.views_t) : bool = {
        var vscwp, b;

        vscwp <- map (fun pid => 
                              let (xi,ri,tri) = oget (assoc vsc pid) in
                              (pid, ((ProtocolFunctionality.input pid xs), 
                                     (ArithP.rand pid rwp, ri), 
                                     (tri.`1, (get_local_trace pid trwp, tri.`2))))) cr;
        b <@ D.guess(vscwp);
        return b;
      }
    }.

    module D_WP (D : Privacy.Distinguisher_t) (R : SP_S.Rand_t) = {

      var xs : ProtocolFunctionality.inputs_t
      var cr : SG.GateFunctionality.pid_t list
      var aux : WP_S.aux_t
      var c : ProtocolFunctionality.Circuit.circuit_t

      proc choose(c_: ProtocolFunctionality.Circuit.circuit_t, x : env_input_t, aux_ : WP_S.aux_t) : ProtocolFunctionality.inputs_t * ProtocolFunctionality.pid_t list = {

        c <- c_;
        aux <- aux_;
        (xs,cr) <@ D.choose(c, x, aux);

        return (xs,cr);
      }

      proc guess(ys : ArithP.poutputs_t, vsc : weak_views_t) : bool = {
        var vscsp, b, xspc, rsp, vsp, ysf, ysfc;

        rsp <@ R.gen((aux,c),cr);
        if (valid_rands rsp) {

          ysf <- ProtocolFunctionality.f c xs;
          ysfc <- map (fun pid => (pid, oget (assoc ysf pid))) cr;
          xspc <- map (fun pid => (pid, ((), (local_output_gates pid (oget (assoc vsc pid)).`1 (oget (assoc vsc pid)).`2 (oget (assoc vsc pid)).`3, witness)))) cr;
          vsp <- SP_S.simulator rsp xspc cr ysfc;

          vscsp <- map (fun pid => (pid, (ProtocolFunctionality.input pid xs, 
                                        ((oget (assoc vsc pid)).`2, (oget (assoc vsp pid)).`2), 
                                        ((oget (assoc vsp pid)).`3.`1,
                                        ((oget (assoc vsc pid)).`3, (oget (assoc vsp pid)).`3.`2))))) cr;
          b <@ D.guess(vscsp);
        } else { b <${0,1}; }
        
        return b;
      }
    }.

    module Simulator = {
      proc simm(c : ProtocolFunctionality.Circuit.circuit_t, xs : PP.ProtocolFunctionality.inputs_t, rs : rands_t, cr : PP.ProtocolFunctionality.pid_t list, zs : PP.ProtocolFunctionality.outputs_t) : views_t = {
        var vsc, rwp, vswp, ysc;
        var rsp, xspc, vsp;

        rwp <- map (fun pid => (pid, fst (rand pid rs))) ProtocolFunctionality.pid_set;
        (ysc, vswp) <- WP_S.simulator c xs rwp cr;

        rsp <- map (fun pid => (pid, snd (rand pid rs))) ProtocolFunctionality.pid_set;
          xspc <- map (fun pid => (pid, ((), (local_output_gates pid (oget (assoc vswp pid)).`1 (oget (assoc vswp pid)).`2 (oget (assoc vswp pid)).`3, witness<:share_t>)))) cr;
        vsp <- SP_S.simulator rsp xspc cr zs;

        vsc <- map (fun pid => (pid, (ProtocolFunctionality.input pid xs, 
                                      ((oget (assoc vswp pid)).`2, (oget (assoc vsp pid)).`2), 
                                      ((oget (assoc vsp pid)).`3.`1,
                                      ((oget (assoc vswp pid)).`3, (oget (assoc vsp pid)).`3.`2))))) cr;

        return vsc;
      }
    }.

    module R_PP (R_WP : WP_S.Rand_t) (R_SP : SP_S.Rand_t) : Privacy.Rand_t = {
      proc gen(c : ProtocolFunctionality.Circuit.circuit_t, cr : ProtocolFunctionality.pid_t list, aux : aux_t) : rands_t = {
        var rwp, rsp, rs;

        rwp <@ R_WP.gen(c, cr, aux);
        rsp <@ R_SP.gen((aux,c),cr);

        rs <- [];
        if (ArithP.valid_rands c rwp /\ valid_rands rsp) {
          rs <- map (fun pid => (pid, (ArithP.rand pid rwp, SG.rand pid rsp))) pid_set;
        }

        return rs;
      }
    }.

    declare module D : Privacy.Distinguisher_t{D_SP,D_WP}.
    declare module R_WP : WP_S.Rand_t{D,D_SP,D_WP}.
    declare module R_SP : SP_S.Rand_t{D,D_SP,R_WP,D_WP}.
    axiom r_sp_gen_ll : islossless R_SP.gen.

    lemma neg_forall (p : 'a -> bool) : !(forall x, p x) <=> exists x, ! p x by smt().
    lemma neg_exists (p : 'a -> bool) : !(exists x, p x) <=> forall x, ! p x by smt().

    local module Game1 = Privacy.Game(D, R_PP(R_WP, R_SP), RealEvaluator1).

    lemma strong_equiv_real :
      equiv [ Privacy.GameReal(D, R_PP(R_WP, R_SP)).main ~ SP_S.GameReal(D_SP(D, R_WP), R_SP).main :
                ={x} /\ aux{2} = (aux{1},c{1}) /\ ={glob D, glob R_SP, glob R_WP} ==> ={res} ].
    proof.
      proc; inline*; sp.
      seq 1 1 : (#pre /\ xs{1} = D_SP.xs{2} /\ cr{1} = D_SP.cr{2}); first
        by call (_ : true); skip => /#. 
      sp; seq 1 1 : (#pre /\ rwp{1} = D_SP.rwp{2}); first 
        by call (_ : true); skip => /#. 
      case (ProtocolFunctionality.valid_inputs c{2} D_SP.xs{2}); last first.
        rcondf{2} 2; first by move => &m; wp; skip => /#. 
        rcondf{1} 5; first by move => &m; wp; call (_:true); skip => /#. 
        rcondf{2} 4; first move => &m; wp; call (_:true); wp; skip; smt(pid_set_size n_pos).
        by rnd; wp; call (_ : true); wp; skip => /#.
      case (WP_S.valid_corrupted_set D_SP.cr{2}); last first.
        rcondf{2} 2; first by move => &m; wp; skip => /#. 
        rcondf{1} 5; first by move => &m; wp; call (_:true); skip => /#. 
        rcondf{2} 4; first move => &m; wp; call (_:true); wp; skip; smt(pid_set_size n_pos).
        by rnd; wp; call (_ : true); wp; skip => /#.
      case (ArithP.valid_rands c{2} D_SP.rwp{2}); last first.
        rcondf{2} 2; first by move => &m; wp; skip => /#. 
        rcondf{1} 3; first by move => &m; wp; call (_:true); skip => /#. 
        rcondf{2} 4; first move => &m; wp; call (_:true); wp; skip; smt(pid_set_size n_pos).
        rcondf{1} 4; first move => &m; wp; call (_:true); wp; skip; smt(pid_set_size n_pos).
        by rnd; wp; call (_ : true); wp; skip => /#.
      rcondt{2} 2; first by move => &m; wp; skip => /#. 
      sp; seq 1 1 : (#pre /\ rsp{1} = r{2}); first by call (_ : true); skip; progress.
      case (valid_rands r{2}); last first.
        rcondf{2} 1; first by move => &m; wp; skip => /#. 
        rcondf{1} 2; first by move => &m; wp; skip => /#. 
        rcondf{1} 3; first move => &m; wp; skip; smt(pid_set_size n_pos).
        by rnd; wp; skip => /#.
      rcondt{1} 2; first by move => &m; wp; skip => /#. 
      sp 3 0; if; last by rnd. progress.
        * by rewrite -map_comp /(\o) /= map_id /=.
move : H H0 H2 H4 H5; elim (c{1}) => topo gg /=.
elim topo => np ns m q /=.
progress.
rewrite /sinput /input /=.
rewrite /pgates_fgates_valid /=.
progress.
move : (correct_eval_gates (np,ns,m,q) gg D_SP.rwp{2} D_SP.xs{2} ((oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
map SecretSharingScheme.reconstruct
     (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
have ->: (ArithmeticCircuit.Circuit.valid_topology (np, ns, m, q)) by smt().
have ->: (ArithmeticCircuit.valid_gates ((np, ns, m, q), gg)) by smt().
have ->: all
   (fun (pid : pid_t) => gates_valid_rand gg (oget (assoc D_SP.rwp{2} pid))) pid_set.
rewrite allP; progress.
move : H2; rewrite /valid_rands /=.
progress.
move : (H8 x1).
rewrite H7.
by rewrite /valid_rand /=.
have ->: valid_inputs_topology (np, ns, m, q) D_SP.xs{2} by smt().

have ->: pinput_finput_valid
   (((np, ns, m, q), witness), D_SP.xs{2},
    ((oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
     map SecretSharingScheme.reconstruct
       (map
          (fun (k : int) =>
             map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`2 k))
               SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite /pinput_finput_valid /=.
rewrite !size_map.
move : H0.
rewrite /valid_inputs /= /valid_inputs_topology /= /pinput /sinput /input /=.
progress.
by rewrite H8; first by smt(pid_set_size n_pos).
by rewrite size_range /max => /#.
by rewrite H8; first by smt(pid_set_size n_pos).
by rewrite H9; first by smt(pid_set_size n_pos).
rewrite !map_assoc //=.
rewrite /pinput /input /=.
move : (H11 k); rewrite H13 H14 /=.
progress.
move : H16; rewrite allP; progress.
have : (pid, nth witness (oget (assoc D_SP.xs{2} pid)).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_SP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
by exists pid => /=.
have : ((head witness SecretSharingScheme.pid_set), nth witness (oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_SP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
exists (head witness SecretSharingScheme.pid_set) => /=.
smt(pid_set_size n_pos).
smt().

rewrite -!map_comp /(\o) /=.
rewrite (nth_map witness).
by rewrite size_range => /#.
simplify.
rewrite /reconstruct.
congr.
rewrite -eq_in_map => pid'; progress.
rewrite nth_range 1:/#.
simplify.
rewrite /input.
done.

simplify.
rewrite /pgates_fgates_valid /=.
progress.

exists r0 (eval_gates gg
      ((oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
       map SecretSharingScheme.reconstruct
         (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite H10.
rewrite H9.
progress.
rewrite H11.
rewrite /sinput /input /=.
have ->: map
  (fun (pid : GateFunctionality.pid_t) =>
     (pid,
      (oget
         (assoc
            (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys{2} pid0), witness<:share_t>)))) ProtocolFunctionality.pid_set)
            pid)).`2.`1)) GateFunctionality.pid_set = 
map
  (fun (pid : GateFunctionality.pid_t) =>
     (pid, oget (assoc ys{2} pid))) pid_set.
rewrite -eq_in_map => pid; progress.
by rewrite !map_assoc //=.
have ->: map (fun (pid : GateFunctionality.pid_t) => (pid, oget (assoc ys{2} pid))) pid_set = ys{2}.
rewrite (eq_assoc_map ys{2}).
smt.
have ->: unzip1 ys{2} = pid_set by smt.
by rewrite -eq_in_map; progress; rewrite !map_assoc //=.
smt().
        * by smt().
        * by smt().
        * by rewrite -map_comp /(\o) /= map_id /=.
          move : H2; rewrite /valid_rands /= /pid_set /=; progress.
          by move : (H8 pid); rewrite H7 /= /rand !map_assoc //= /rand /#. 
        * by smt().
        * by smt().
      wp; call (_ : true); wp; skip; progress.
      rewrite -eq_in_map => pid; progress.
      rewrite /input /rand /output /trace.
      rewrite !map_assoc //=; first by move : H2; rewrite /valid_corrupted_set; progress => /#.
      progress; rewrite /protocol /= /rand /=. 
      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ProtocolFunctionality.pid_t) => (pid1, (oget (assoc D_SP.rwp{2} pid1), oget (assoc r{2} pid1)))) ProtocolFunctionality.pid_set) pid0)).`2)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, rand pid r{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc //= !map_assoc //=.
      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ProtocolFunctionality.pid_t) => (pid1, (oget (assoc D_SP.rwp{2} pid1), oget (assoc r{2} pid1)))) ProtocolFunctionality.pid_set) pid0)).`1)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, ArithP.rand pid D_SP.rwp{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid''; progress; rewrite !map_assoc //= !map_assoc //=.
      rewrite /protocol /eval_circuit /=; move : H H0 H2 H4 H5.
      elim (c{1}) => topo gg /=; progress.
      have : exists (trwp, ys), (trwp, ys) = eval_gates gg (map (fun (pid0 : pid_t) => (pid0, ArithP.rand pid0 D_SP.rwp{2})) ProtocolFunctionality.pid_set) D_SP.xs{2}
        by exists (eval_gates gg (map (fun (pid0 : pid_t) => (pid0, ArithP.rand pid0 D_SP.rwp{2})) ProtocolFunctionality.pid_set) D_SP.xs{2}).`1
                  (eval_gates gg (map (fun (pid0 : pid_t) => (pid0, ArithP.rand pid0 D_SP.rwp{2})) ProtocolFunctionality.pid_set) D_SP.xs{2}).`2 => /#.
      progress; rewrite -H8 /=; move : H8.
      have : exists (trsp, zs), (trsp, zs) = gate (map (fun (pid0 : pid_t) => (pid0, rand pid0 r{2})) ProtocolFunctionality.pid_set) (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys0 pid0), witness)))) ProtocolFunctionality.pid_set)
        by exists (gate (map (fun (pid0 : pid_t) => (pid0, rand pid0 r{2})) ProtocolFunctionality.pid_set) (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys0 pid0), witness)))) ProtocolFunctionality.pid_set)).`1
                  (gate (map (fun (pid0 : pid_t) => (pid0, rand pid0 r{2})) ProtocolFunctionality.pid_set) (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys0 pid0), witness)))) ProtocolFunctionality.pid_set)).`2 => /#.
      progress; rewrite -H8 /=.
      rewrite !map_assoc 1:/# //=; split. 
move : H9.
have ->: eval_gates gg
  (map (fun (pid0 : pid_t) => (pid0, ArithP.rand pid0 D_SP.rwp{2})) ProtocolFunctionality.pid_set) D_SP.xs{2} = eval_gates gg
  D_SP.rwp{2} D_SP.xs{2}.
congr.


          rewrite eq_assoc_map; first by move : H2; rewrite /valid_rands; smt(pid_set_uniq). 
          have ->: (unzip1 D_SP.rwp{2}) = pid_set by move : H2; rewrite /valid_rands; smt(pid_set_uniq). 
          rewrite -eq_in_map => pid'; progress.
          by rewrite /rand map_assoc //=.

move : H8.
have ->: gate (map (fun (pid0 : pid_t) => (pid0, rand pid0 r{2})) ProtocolFunctionality.pid_set)
  (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys0 pid0), witness))))
     ProtocolFunctionality.pid_set) = gate r{2}
  (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys0 pid0), witness))))
     ProtocolFunctionality.pid_set).
congr.
          rewrite eq_assoc_map; first by move : H2; rewrite /valid_rands; smt(pid_set_uniq). 
          have ->: (unzip1 r{2}) = pid_set by move : H2; rewrite /valid_rands; smt(pid_set_uniq). 
          rewrite -eq_in_map => pid'; progress.
          by rewrite /rand map_assoc //=.
rewrite /output /= /trace.
progress.
have <-: ys0 = ys{2} by smt().
smt().

move : H9.
have ->: eval_gates gg
  (map (fun (pid0 : pid_t) => (pid0, ArithP.rand pid0 D_SP.rwp{2})) ProtocolFunctionality.pid_set) D_SP.xs{2} = eval_gates gg
  D_SP.rwp{2} D_SP.xs{2}.
congr.


          rewrite eq_assoc_map; first by move : H2; rewrite /valid_rands; smt(pid_set_uniq). 
          have ->: (unzip1 D_SP.rwp{2}) = pid_set by move : H2; rewrite /valid_rands; smt(pid_set_uniq). 
          rewrite -eq_in_map => pid'; progress.
          by rewrite /rand map_assoc //=.

move : H8.
have ->: gate (map (fun (pid0 : pid_t) => (pid0, rand pid0 r{2})) ProtocolFunctionality.pid_set)
  (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys0 pid0), witness))))
     ProtocolFunctionality.pid_set) = gate r{2}
  (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys0 pid0), witness))))
     ProtocolFunctionality.pid_set).
congr.
          rewrite eq_assoc_map; first by move : H2; rewrite /valid_rands; smt(pid_set_uniq). 
          have ->: (unzip1 r{2}) = pid_set by move : H2; rewrite /valid_rands; smt(pid_set_uniq). 
          rewrite -eq_in_map => pid'; progress.
          by rewrite /rand map_assoc //=.
rewrite /output /= /trace.
progress.
smt().

have <-: ys0 = ys{2} by smt().
smt().
    qed.

    local lemma strong_equiv_ideal :
      equiv [ Game1.main ~ SP_S.GameIdeal(D_SP(D, R_WP), R_SP).main :
                ={x} /\ aux{2} = (aux{1},c{1}) /\ ={glob D, glob R_SP, glob R_WP} ==> ={res} ].
    proof.
      proc; inline*; sp.
      seq 1 1 : (#pre /\ xs{1} = D_SP.xs{2} /\ cr{1} = D_SP.cr{2}); first
        by call (_ : true); skip => /#. 
      sp; seq 1 1 : (#pre /\ rwp{1} = D_SP.rwp{2}); first 
        by call (_ : true); skip => /#. 
      case (ProtocolFunctionality.valid_inputs c{2} D_SP.xs{2}); last first.
        rcondf{2} 2; first by move => &m; wp; skip => /#. 
        rcondf{1} 5; first by move => &m; wp; call (_:true); skip => /#. 
        rcondf{2} 4; first move => &m; wp; call (_:true); wp; skip; smt(pid_set_size n_pos).
        by rnd; wp; call (_ : true); wp; skip => /#.
      case (WP_S.valid_corrupted_set D_SP.cr{2}); last first.
        rcondf{2} 2; first by move => &m; wp; skip => /#. 
        rcondf{1} 5; first by move => &m; wp; call (_:true); skip => /#. 
        rcondf{2} 4; first move => &m; wp; call (_:true); wp; skip; smt(pid_set_size n_pos).
        by rnd; wp; call (_ : true); wp; skip => /#.
      case (ArithP.valid_rands c{2} D_SP.rwp{2}); last first.
        rcondf{2} 2; first by move => &m; wp; skip => /#. 
        rcondf{1} 3; first by move => &m; wp; call (_:true); skip => /#. 
        rcondf{2} 4; first move => &m; wp; call (_:true); wp; skip; smt(pid_set_size n_pos).
        rcondf{1} 4; first move => &m; wp; call (_:true); wp; skip; smt(pid_set_size n_pos).
        by rnd; wp; call (_ : true); wp; skip => /#.
      rcondt{2} 2; first by move => &m; wp; skip => /#. 
      sp; seq 1 1 : (#pre /\ rsp{1} = r{2}); first by call (_ : true); skip; progress.
      case (valid_rands r{2}); last first.
        rcondf{2} 1; first by move => &m; wp; skip => /#. 
        rcondf{1} 2; first by move => &m; wp; skip => /#. 
        rcondf{1} 3; first move => &m; wp; skip; smt(pid_set_size n_pos).
        by rnd; wp; skip => /#.
      rcondt{1} 2; first by move => &m; wp; skip => /#. 
      sp 3 0; if; last by rnd. progress.
        * by rewrite -map_comp /(\o) /= map_id /=.
move : H H0 H2 H4 H5; elim (c{1}) => topo gg /=.
elim topo => np ns m q /=.
progress.
rewrite /sinput /input /=.

move : (correct_eval_gates (np,ns,m,q) gg D_SP.rwp{2} D_SP.xs{2} ((oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
map SecretSharingScheme.reconstruct
     (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
have ->: (ArithmeticCircuit.Circuit.valid_topology (np, ns, m, q)) by smt().
have ->: (ArithmeticCircuit.valid_gates ((np, ns, m, q), gg)) by smt().
have ->: all
   (fun (pid : pid_t) => gates_valid_rand gg (oget (assoc D_SP.rwp{2} pid))) pid_set.
rewrite allP; progress.
move : H2; rewrite /valid_rands /=.
progress.
move : (H8 x1).
rewrite H7.
by rewrite /valid_rand /=.
have ->: valid_inputs_topology (np, ns, m, q) D_SP.xs{2} by smt().

have ->: pinput_finput_valid
   (((np, ns, m, q), witness), D_SP.xs{2},
    ((oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
     map SecretSharingScheme.reconstruct
       (map
          (fun (k : int) =>
             map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`2 k))
               SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite /pinput_finput_valid /=.
rewrite !size_map.
move : H0.
rewrite /valid_inputs /= /valid_inputs_topology /= /pinput /sinput /input /=.
progress.
by rewrite H8; first by smt(pid_set_size n_pos).
by rewrite size_range /max => /#.
by rewrite H8; first by smt(pid_set_size n_pos).
by rewrite H9; first by smt(pid_set_size n_pos).
rewrite !map_assoc //=.
rewrite /pinput /input /=.
move : (H11 k); rewrite H13 H14 /=.
progress.
move : H16; rewrite allP; progress.
have : (pid, nth witness (oget (assoc D_SP.xs{2} pid)).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_SP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
by exists pid => /=.
have : ((head witness SecretSharingScheme.pid_set), nth witness (oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_SP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
exists (head witness SecretSharingScheme.pid_set) => /=.
smt(pid_set_size n_pos).
smt().

rewrite -!map_comp /(\o) /=.
rewrite (nth_map witness).
by rewrite size_range => /#.
simplify.
rewrite /reconstruct.
congr.
rewrite -eq_in_map => pid'; progress.
rewrite nth_range 1:/#.
simplify.
rewrite /input.
done.

simplify.
rewrite /pgates_fgates_valid /=.
progress.

exists r0 (eval_gates gg
      ((oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
       map SecretSharingScheme.reconstruct
         (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite H10.
rewrite H9.
progress.
rewrite H11.
rewrite /sinput /input /=.
have ->: map
  (fun (pid : GateFunctionality.pid_t) =>
     (pid,
      (oget
         (assoc
            (map (fun (pid0 : pid_t) => (pid0, (tt, (oget (assoc ys{2} pid0), witness<:share_t>)))) ProtocolFunctionality.pid_set)
            pid)).`2.`1)) GateFunctionality.pid_set = 
map
  (fun (pid : GateFunctionality.pid_t) =>
     (pid, oget (assoc ys{2} pid))) pid_set.
rewrite -eq_in_map => pid; progress.
by rewrite !map_assoc //=.
have ->: map (fun (pid : GateFunctionality.pid_t) => (pid, oget (assoc ys{2} pid))) pid_set = ys{2}.
rewrite (eq_assoc_map ys{2}).
smt.
have ->: unzip1 ys{2} = pid_set by smt.
by rewrite -eq_in_map; progress; rewrite !map_assoc //=.
smt().

        * by smt().
        * by smt().
        * by rewrite -map_comp /(\o) /= map_id /=.
          move : H2; rewrite /valid_rands /= /pid_set /=; progress.
          by move : (H8 pid); rewrite H7 /= /rand !map_assoc //= /rand /#. 
        * by smt().
        * by smt().
      wp; call (_ : true); wp; skip; progress.
      rewrite -eq_in_map => pid; progress.
      rewrite /input /rand /output /trace.
      rewrite !map_assoc //=; first by move : H2; rewrite /valid_corrupted_set; progress => /#.
      progress; rewrite /protocol /=. 
      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ProtocolFunctionality.pid_t) => (pid1, (oget (assoc D_SP.rwp{2} pid1), oget (assoc r{2} pid1)))) ProtocolFunctionality.pid_set) pid0)).`2)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, rand pid r{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc //= !map_assoc //=.
rewrite /f /= /sinput /input /=.
      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ProtocolFunctionality.pid_t) => (pid1, (oget (assoc D_SP.rwp{2} pid1), oget (assoc r{2} pid1)))) ProtocolFunctionality.pid_set) pid0)).`1)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, ArithP.rand pid D_SP.rwp{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid''; progress; rewrite !map_assoc //= !map_assoc //=.
      rewrite /protocol /eval_circuit /=; move : H H0 H2 H4 H5.
      elim (c{1}) => topo gg /=; progress.
      have : exists (trwp, ys), (trwp, ys) = eval_gates gg (map (fun (pid0 : pid_t) => (pid0, ArithP.rand pid0 D_SP.rwp{2})) ProtocolFunctionality.pid_set) D_SP.xs{2}
        by exists (eval_gates gg (map (fun (pid0 : pid_t) => (pid0, ArithP.rand pid0 D_SP.rwp{2})) ProtocolFunctionality.pid_set) D_SP.xs{2}).`1
                  (eval_gates gg (map (fun (pid0 : pid_t) => (pid0, ArithP.rand pid0 D_SP.rwp{2})) ProtocolFunctionality.pid_set) D_SP.xs{2}).`2 => /#.
      progress; rewrite -H8 /=; progress.
      have H10 : ys{2} = ys1.
have : (map (fun (pid0 : pid_t) => (pid0, (ArithP.rand pid0 D_SP.rwp{2}))) ProtocolFunctionality.pid_set) = D_SP.rwp{2}.
rewrite /rand eq_assoc_map. smt.
have ->: (unzip1 D_SP.rwp{2}) = pid_set by smt.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.
smt().
rewrite !H10.

      have ->: (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, oget (assoc (map (fun (pid1 : pid_t) => (pid1, (tt, (oget (assoc ys1 pid1), witness<:share_t>)))) ProtocolFunctionality.pid_set) pid0))) D_SP.cr{2}) = (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, (tt, (oget (assoc ys1 pid0), witness)))) D_SP.cr{2})
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc 1,2:/# => /= /#.
      rewrite /input /=.
progress.

have H9 : eval_gates gg (map (fun (pid0 : pid_t) => (pid0, (rand pid0 D_SP.rwp{2})%ArithP)) ProtocolFunctionality.pid_set)
      D_SP.xs{2} = eval_gates gg
  D_SP.rwp{2} D_SP.xs{2}.
congr.
          rewrite eq_assoc_map; first by move : H2; rewrite /valid_rands; smt(pid_set_uniq). 
          have ->: (unzip1 D_SP.rwp{2}) = pid_set by move : H2; rewrite /valid_rands; smt(pid_set_uniq). 
          rewrite -eq_in_map => pid''; progress.
          by rewrite /rand map_assoc //=.
      rewrite /f /=.
rewrite /sinput /input /=.
      have ->: (map (fun (pid2 : GateFunctionality.pid_t) =>
                                       (pid2,
                                        (oget
                                           (assoc
                                              (map
                                                 (fun (pid3 : pid_t) => (pid3, (tt, (oget (assoc ys1 pid3), witness<:share_t>))))
                                                 pid_set) pid2)).`2.`1)) GateFunctionality.pid_set) = (map
                (fun (pid0 : GateFunctionality.pid_t) =>
                   (pid0,  oget (assoc ys1 pid0))) GateFunctionality.pid_set).
        by rewrite -eq_in_map /input => pid'; progress; rewrite !map_assoc 1,2:/# => //=. 

      have ->: (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, oget (assoc (map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1,reconstruct (map (fun (pid0_0 : GateFunctionality.pid_t) => (pid0_0, oget (assoc ys1 pid0_0))) GateFunctionality.pid_set))) GateFunctionality.pid_set) pid0))) D_SP.cr{2}) = map (fun pid => (pid, reconstruct ys{2})) D_SP.cr{2}.
        rewrite -eq_in_map /input => pid'; progress; rewrite !map_assoc 1:/# //=. 

move : H0 H2 H4 H5; elim topo => np ns m q /=.
progress.

move : (correct_eval_gates (np,ns,m,q) gg D_SP.rwp{2} D_SP.xs{2} ((oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
map SecretSharingScheme.reconstruct
     (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
have ->: (ArithmeticCircuit.Circuit.valid_topology (np, ns, m, q)) by smt().
have ->: (ArithmeticCircuit.valid_gates ((np, ns, m, q), gg)) by smt().
have ->: all
   (fun (pid : pid_t) => gates_valid_rand gg (oget (assoc D_SP.rwp{2} pid))) pid_set.
rewrite allP; progress.
move : H2; rewrite /valid_rands /=.
progress.
move : (H13 x1).
rewrite H12.
by rewrite /valid_rand /=.
have ->: valid_inputs_topology (np, ns, m, q) D_SP.xs{2} by smt().

have ->: pinput_finput_valid
   (((np, ns, m, q), witness), D_SP.xs{2},
    ((oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
     map SecretSharingScheme.reconstruct
       (map
          (fun (k : int) =>
             map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`2 k))
               SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite /pinput_finput_valid /=.
rewrite !size_map.
move : H0.
rewrite /valid_inputs /= /valid_inputs_topology /= /pinput /sinput /input /=.
progress.
by rewrite H13; first by smt(pid_set_size n_pos).
by rewrite size_range /max => /#.
by rewrite H13; first by smt(pid_set_size n_pos).
by rewrite H14; first by smt(pid_set_size n_pos).
rewrite !map_assoc //=.
rewrite /pinput /input /=.
move : (H16 k); rewrite H18 H19 /=.
progress.
move : H21; rewrite allP; progress.
have : (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_SP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
by exists pid0 => /=.
have : ((head witness SecretSharingScheme.pid_set), nth witness (oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_SP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
exists (head witness SecretSharingScheme.pid_set) => /=.
smt(pid_set_size n_pos).
smt().

rewrite -!map_comp /(\o) /=.
rewrite (nth_map witness).
by rewrite size_range => /#.
simplify.
rewrite /reconstruct.
congr.
rewrite -eq_in_map => pid''; progress.
rewrite nth_range 1:/#.
simplify.
rewrite /input.
done.

simplify.
rewrite /pgates_fgates_valid /=.
progress.

move : H16.
rewrite -H13.
progress.
have ->: ys{2} = (eval_gates gg D_SP.rwp{2} D_SP.xs{2}).`2 by smt().
rewrite (eq_assoc_map (eval_gates gg D_SP.rwp{2} D_SP.xs{2}).`2).
smt(pid_set_uniq).
have ->: (unzip1 (eval_gates gg D_SP.rwp{2} D_SP.xs{2}).`2) = pid_set by smt().
congr; rewrite -eq_in_map; progress.
smt().

have ->: (map (fun (pid0 : pid_t) => (pid0, rand pid0 r{2})) ProtocolFunctionality.pid_set) = r{2}.
rewrite /rand eq_assoc_map; first by smt.
have ->: (unzip1 r{2}) = pid_set by smt.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.

have ->: (map
             (fun (pid0 : GateFunctionality.pid_t) =>
                (pid0,
                 oget
                   (assoc
                      (map (fun (pid1 : pid_t) => (pid1, (tt, (oget (assoc ys1 pid1), witness<:share_t>)))) ProtocolFunctionality.pid_set)
                      pid0))) D_SP.cr{2}) =
(map (fun (pid0 : GateFunctionality.pid_t) => (pid0, (tt, (oget (assoc ys1 pid0), witness)))) D_SP.cr{2}).
rewrite -eq_in_map; progress.
by rewrite !map_assoc; first by smt().

have ->: (map
             (fun (pid0 : GateFunctionality.pid_t) =>
                (pid0,
                 oget
                   (assoc
                      (map
                         (fun (pid1 : SecretSharingScheme.pid_t) =>
                            (pid1,
                             reconstruct
                               (map
                                  (fun (pid2 : GateFunctionality.pid_t) =>
                                     (pid2,
                                      (oget
                                         (assoc
                                            (map (fun (pid3 : pid_t) => (pid3, (tt, (oget (assoc ys1 pid3), witness<:share_t>))))
                                               ProtocolFunctionality.pid_set) pid2)).`2.`1)) GateFunctionality.pid_set)))
                         GateFunctionality.pid_set) pid0))) D_SP.cr{2}) = 
(map
             (fun (pid0 : GateFunctionality.pid_t) =>
                (pid0,
                 oget
                   (assoc
                      (map
                         (fun (pid1 : SecretSharingScheme.pid_t) =>
                            (pid1,
                             reconstruct
                               (map
                                  (fun (pid2 : GateFunctionality.pid_t) =>
                                     (pid2, oget (assoc ys1 pid2)))
                                       GateFunctionality.pid_set)))
                         GateFunctionality.pid_set) pid0))) D_SP.cr{2}).
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first 2 by smt().
have ->: (map
     (fun (pid2 : GateFunctionality.pid_t) =>
        (pid2,
         (oget
            (assoc
               (map (fun (pid3 : pid_t) => (pid3, (tt, (oget (assoc ys1 pid3), witness<:share_t>))))
                  ProtocolFunctionality.pid_set) pid2)).`2.`1)) GateFunctionality.pid_set) = 
(map
     (fun (pid2 : GateFunctionality.pid_t) =>
        (pid2, oget (assoc ys1 pid2))) GateFunctionality.pid_set).
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=. 
done.

have ->: (map
               (fun (pid0 : GateFunctionality.pid_t) =>
                  (pid0,
                   oget
                     (assoc
                        (map
                           (fun (pid1 : SecretSharingScheme.pid_t) =>
                              (pid1,
                               reconstruct
                                 (map (fun (pid0_0 : GateFunctionality.pid_t) => (pid0_0, oget (assoc ys1 pid0_0)))
                                    GateFunctionality.pid_set))) GateFunctionality.pid_set) pid0))) D_SP.cr{2}) = (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, reconstruct ys{2})) D_SP.cr{2}).
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first by smt().

move : H0 H2 H4 H5; elim topo => np ns m q /=.
progress.

move : (correct_eval_gates (np,ns,m,q) gg D_SP.rwp{2} D_SP.xs{2} ((oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
map SecretSharingScheme.reconstruct
     (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
have ->: (ArithmeticCircuit.Circuit.valid_topology (np, ns, m, q)) by smt().
have ->: (ArithmeticCircuit.valid_gates ((np, ns, m, q), gg)) by smt().
have ->: all
   (fun (pid : pid_t) => gates_valid_rand gg (oget (assoc D_SP.rwp{2} pid))) pid_set.
rewrite allP; progress.
move : H2; rewrite /valid_rands /=.
progress.
move : (H13 x2).
rewrite H12.
by rewrite /valid_rand /=.
have ->: valid_inputs_topology (np, ns, m, q) D_SP.xs{2} by smt().

have ->: pinput_finput_valid
   (((np, ns, m, q), witness), D_SP.xs{2},
    ((oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
     map SecretSharingScheme.reconstruct
       (map
          (fun (k : int) =>
             map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`2 k))
               SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite /pinput_finput_valid /=.
rewrite !size_map.
move : H0.
rewrite /valid_inputs /= /valid_inputs_topology /= /pinput /sinput /input /=.
progress.
by rewrite H13; first by smt(pid_set_size n_pos).
by rewrite size_range /max => /#.
by rewrite H13; first by smt(pid_set_size n_pos).
by rewrite H14; first by smt(pid_set_size n_pos).
rewrite !map_assoc //=.
rewrite /pinput /input /=.
move : (H16 k); rewrite H18 H19 /=.
progress.
move : H21; rewrite allP; progress.
have : (pid0, nth witness (oget (assoc D_SP.xs{2} pid0)).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_SP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
by exists pid0 => /=.
have : ((head witness SecretSharingScheme.pid_set), nth witness (oget (assoc D_SP.xs{2} (head witness SecretSharingScheme.pid_set))).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_SP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
exists (head witness SecretSharingScheme.pid_set) => /=.
smt(pid_set_size n_pos).
smt().

rewrite -!map_comp /(\o) /=.
rewrite (nth_map witness).
by rewrite size_range => /#.
simplify.
rewrite /reconstruct.
congr.
rewrite -eq_in_map => pid'; progress.
rewrite nth_range 1:/#.
simplify.
rewrite /input.
done.

simplify.
rewrite /pgates_fgates_valid /=.
progress.

move : H16.
rewrite -H13.
progress.
have ->: ys{2} = (eval_gates gg D_SP.rwp{2} D_SP.xs{2}).`2 by smt().
rewrite (eq_assoc_map (eval_gates gg D_SP.rwp{2} D_SP.xs{2}).`2).
smt(pid_set_uniq).
have ->: (unzip1 (eval_gates gg D_SP.rwp{2} D_SP.xs{2}).`2) = pid_set by smt().
congr; rewrite -eq_in_map; progress.
smt().

      have : exists (xi, ri, tri), (xi, ri, tri) = oget (assoc (simulator r{2} (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, (tt, (oget (assoc ys1 pid0), witness)))) D_SP.cr{2}) D_SP.cr{2} (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, reconstruct ys{2})) D_SP.cr{2})) pid)
        by exists (oget (assoc (simulator r{2} (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, (tt, (oget (assoc ys1 pid0), witness)))) D_SP.cr{2}) D_SP.cr{2} (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, reconstruct ys{2})) D_SP.cr{2})) pid)).`1
                  (oget (assoc (simulator r{2} (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, (tt, (oget (assoc ys1 pid0), witness)))) D_SP.cr{2}) D_SP.cr{2} (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, reconstruct ys{2})) D_SP.cr{2})) pid)).`2
                  (oget (assoc (simulator r{2} (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, (tt, (oget (assoc ys1 pid0), witness)))) D_SP.cr{2}) D_SP.cr{2} (map (fun (pid0 : GateFunctionality.pid_t) => (pid0, reconstruct ys{2})) D_SP.cr{2})) pid)).`3 => /#.
      progress. rewrite -!H11 /=.
smt().
    qed.

    local lemma adv_strong_hop &m c x aux : 
      Pr[Privacy.GameReal(D, R_PP(R_WP, R_SP)).main(c,x,aux) @ &m : res] - 
      Pr[Game1.main(c,x,aux) @ &m : res] <=
      Pr[SP_S.GameReal(D_SP(D, R_WP), R_SP).main(x,(aux,c)) @ &m : res] -
      Pr[SP_S.GameIdeal(D_SP(D, R_WP), R_SP).main(x,(aux,c)) @ &m : res].
    proof.
      have ->: Pr[Privacy.GameReal(D, R_PP(R_WP, R_SP)).main(c,x,aux) @ &m : res] =
              Pr[SP_S.GameReal(D_SP(D, R_WP), R_SP).main(x,(aux,c)) @ &m : res].
        by byequiv strong_equiv_real => /#.
      have ->: Pr[Game1.main(c,x,aux) @ &m : res] = 
               Pr[SP_S.GameIdeal(D_SP(D, R_WP), R_SP).main(x,(aux,c)) @ &m : res]
        by byequiv strong_equiv_ideal => /= /#.
      by done.
    qed.

    local lemma weak_equiv_real :
      equiv [ Game1.main ~ WP_S.GameReal(D_WP(D, R_SP), R_WP).main :
                ={c,x,aux} /\ ={glob D, glob R_SP, glob R_WP} ==> ={res} ].
    proof.
      proc; inline*; sp.
      seq 1 1 : (#pre /\ xs{1} = D_WP.xs{2} /\ cr{1} = D_WP.cr{2}); first
        by call (_ : true); skip => /#. 
      sp; seq 1 1 : (#pre /\ rwp{1} = r{2}); first 
        by call (_ : true); skip => /#. 
      case (ProtocolFunctionality.valid_inputs c{2} xs{2}); last first.
        rcondf{2} 1; first by move => &m; wp; skip => /#. 
        rcondf{1} 5; first by move => &m; wp; call (_:true); skip => /#. 
        by rnd; wp; call{1} r_sp_gen_ll; wp; skip => /#.
      case (WP_S.valid_corrupted_set cr{2}); last first.
        rcondf{2} 1; first by move => &m; wp; skip => /#. 
        rcondf{1} 5; first by move => &m; wp; call (_:true); skip => /#. 
        by rnd; wp; call{1} r_sp_gen_ll; wp; skip => /#.
      case (ArithP.valid_rands c{2} r{2}); last first.
        rcondf{2} 1; first by move => &m; wp; skip => /#. 
        rcondf{1} 3; first by move => &m; wp; call (_:true); skip => /#. 
        rcondf{1} 4; first move => &m; wp; call (_:true); wp; skip; smt(pid_set_size n_pos).
        by rnd; wp; call{1} r_sp_gen_ll; wp; skip => /#.
      rcondt{2} 1; first by move => &m; wp; skip => /#. 
      sp; seq 1 1 : (#pre /\ rsp{1} = rsp{2}); first by call (_ : true); skip; progress.
      case (valid_rands rsp{2}); last first.
        rcondf{2} 1; first by move => &m; wp; skip => /#. 
        rcondf{1} 2; first by move => &m; wp; skip => /#. 
        rcondf{1} 3; first move => &m; wp; skip; smt(pid_set_size n_pos).
        by wp; rnd; wp; skip => /#.
      rcondt{1} 2; first by move => &m; wp; skip => /#. 
      sp 3 0; if; last by wp; rnd. progress.
        * by rewrite -map_comp /(\o) /= map_id /=.
          move : H2; rewrite /valid_rands /= /pid_set /=; progress.
          by move : (H6 pid); rewrite H5 /= /rand !map_assoc //= /rand /#. 
        * by smt().
        * by smt().
      wp; call (_ : true); wp; skip; progress.
      rewrite -eq_in_map => pid H7 /=.
      rewrite /input /rand /output /trace /view.
      rewrite /protocol /=. 
      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : pid_t) => (pid1, (oget (assoc r{2} pid1), oget (assoc rsp{2} pid1)))) ProtocolFunctionality.pid_set) pid0)).`2)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, rand pid rsp{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc //= !map_assoc //=.
      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : pid_t) => (pid1, (oget (assoc r{2} pid1), oget (assoc rsp{2} pid1)))) ProtocolFunctionality.pid_set) pid0)).`1)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, ArithP.rand pid r{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid''; progress; rewrite !map_assoc //= !map_assoc //=.

move : H H0 H2 H4 H5.
rewrite /protocol /=.
elim (c{2}) => topo gg /=.
elim topo => np ns m q /=.
have : exists (tr', ys), (tr', ys) = eval_circuit gg r{2} D_WP.xs{2}
  by exists (eval_circuit gg r{2} D_WP.xs{2}).`1 (eval_circuit gg r{2} D_WP.xs{2}).`2 => /#.
progress.
move : H0; rewrite -H /=.
progress.
by rewrite !map_assoc; first 2 by smt().
move : H0; rewrite -H /=.
progress.
congr.
congr.
congr.
congr.
rewrite eq_assoc_map; first by smt(correct_domain pid_set_uniq).
have ->: (unzip1 rsp{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
by rewrite /rand !map_assoc //=.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first by smt().
move : (local_output_correct_gates (np,ns,m,q) gg x1 D_WP.xs{2} (map (fun (pid0 : pid_t) => (pid0, (rand pid0 r{2})%ArithP)) ProtocolFunctionality.pid_set)).
have ->: x1 \in pid_set by smt().
simplify.
rewrite /rand /input.
rewrite !map_assoc //=; first 2 by smt().
rewrite !map_assoc //=; first by smt().
have ->: (map (fun (pid0 : pid_t) => (pid0, oget (assoc r{2} pid0))) ProtocolFunctionality.pid_set) = r{2}.
rewrite eq_assoc_map; first by smt(correct_domain pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.
smt().


rewrite -eq_in_map; progress.
(*rewrite !map_assoc //=; first by smt().*)
rewrite /f /=.
rewrite /sinput /input !map_assoc //=; first 2 by smt().

have ->: (map
     (fun (pid0 : GateFunctionality.pid_t) =>
        (pid0,
         (oget
            (assoc
               (map
                  (fun (pid1 : pid_t) =>
                     (pid1,
                      (tt,
                       (oget
                          (assoc
                             (eval_gates gg
                                (map (fun (pid2 : pid_t) => (pid2, (rand pid2 r{2})%ArithP))
                                   ProtocolFunctionality.pid_set) D_WP.xs{2}).`2 pid1), witness<:share_t>)))) pid_set) pid0)).`2.`1))
     GateFunctionality.pid_set) = (map
     (fun (pid0 : GateFunctionality.pid_t) =>
        (pid0, oget
                          (assoc
                             (eval_gates gg
                                r{2} D_WP.xs{2}).`2 pid0)))
     GateFunctionality.pid_set).
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.
rewrite (eq_assoc_map r{2}).
smt(pid_set_uniq).
congr.
congr.
congr.
congr.
have ->: (unzip1 r{2}) = pid_set by smt().
rewrite -eq_in_map; progress.
by rewrite /rand !map_assoc //=.


move : (correct_eval_gates (np,ns,m,q) gg r{2} D_WP.xs{2} ((oget (assoc D_WP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
   map SecretSharingScheme.reconstruct
     (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_WP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
have ->: (ArithmeticCircuit.Circuit.valid_topology (np,ns,m,q)) by smt().
have ->: (ArithmeticCircuit.valid_gates ((np,ns,m,q), gg)) by smt().
have ->: all
   (fun (pid : pid_t) => gates_valid_rand gg (oget (assoc r{2} pid))) pid_set.
rewrite allP; progress.
move : H4; rewrite /valid_rands /=.
progress.
move : (H10 x2).
rewrite H9.
by rewrite /valid_rand /=.
have ->: valid_inputs_topology (np,ns,m,q) D_WP.xs{2} by smt().


have ->: pinput_finput_valid
   (((np,ns,m,q), witness), D_WP.xs{2},
    ((oget (assoc D_WP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
     map SecretSharingScheme.reconstruct
       (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_WP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite /pinput_finput_valid /=.
rewrite !size_map.
move : H2.
rewrite /valid_inputs /= /valid_inputs_topology /= /pinput /sinput /input /=.
progress.
by rewrite H10; first by smt(pid_set_size n_pos).
by rewrite size_range /max => /#.
by rewrite H10; first by smt(pid_set_size n_pos).
by rewrite H11; first by smt(pid_set_size n_pos).
rewrite !map_assoc //=.
rewrite /pinput /input /=.
move : (H13 k); rewrite H15 H16 /=.
progress.
move : H18; rewrite allP; progress.
have : (pid0, nth witness (oget (assoc D_WP.xs{2} pid0)).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_WP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
by exists pid0 => /=.
have : ((head witness SecretSharingScheme.pid_set), nth witness (oget (assoc D_WP.xs{2} (head witness SecretSharingScheme.pid_set))).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_WP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
exists (head witness SecretSharingScheme.pid_set) => /=.
smt(pid_set_size n_pos).
smt().

rewrite -!map_comp /(\o) /=.
rewrite (nth_map witness).
by rewrite size_range => /#.
simplify.
rewrite /reconstruct.
congr.
rewrite -eq_in_map => pid'; progress.
rewrite nth_range 1:/#.
simplify.
rewrite /input.
done.

simplify.
rewrite /pgates_fgates_valid /=.
progress.
(*rewrite (eq_assoc_map ys0).
smt(pid_set_uniq).
congr.
have ->: (unzip1 ys0) = pid_set by smt().
rewrite -eq_in_map; progress.
smt().*)
(*rewrite !map_assoc //=.*)
rewrite /pinput /input /=.
move : H. rewrite /eval_circuit -H10 /=.
progress.
congr.
rewrite (eq_assoc_map (eval_gates gg r{2} D_WP.xs{2}).`2).
smt(pid_set_uniq).
have ->: (unzip1 (eval_gates gg r{2} D_WP.xs{2}).`2) = pid_set by smt().
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.


(*progress.
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
have ->: (map (fun (pid0 : pid_t) => (pid0, (rand pid0 r{2})%ArithP)) ProtocolFunctionality.pid_set) = r{2}.
rewrite (eq_assoc_map r{2}).
smt(pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt().
rewrite -eq_in_map; progress.
rewrite /rand !map_assoc //=.
smt().*)

congr.
congr.
congr.
congr.
congr.
rewrite eq_assoc_map; first by smt(correct_domain pid_set_uniq).
have ->: (unzip1 rsp{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
by rewrite /rand !map_assoc //=.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first by smt().
rewrite /f /=.
 
move : (local_output_correct_gates (np,ns,m,q) gg x1 D_WP.xs{2} r{2}).
have ->: x1 \in pid_set by smt().
simplify.
have ->: (map (fun (pid2 : pid_t) => (pid2, (rand pid2 r{2})%ArithP))
                                  ProtocolFunctionality.pid_set) = r{2}.
rewrite eq_assoc_map; first by smt(pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
by rewrite /rand -eq_in_map; progress; rewrite !map_assoc //=.
rewrite /input /rand.
move : H0; rewrite -H /=.
progress.
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
smt().

rewrite -eq_in_map; progress.
rewrite /f /=.
rewrite /sinput /input !map_assoc //=; first 2 by smt().

have ->: (map
     (fun (pid0 : GateFunctionality.pid_t) =>
        (pid0,
         (oget
            (assoc
               (map
                  (fun (pid1 : pid_t) =>
                     (pid1,
                      (tt,
                       (oget
                          (assoc
                             (eval_gates gg
                                (map (fun (pid2 : pid_t) => (pid2, (rand pid2 r{2})%ArithP))
                                   ProtocolFunctionality.pid_set) D_WP.xs{2}).`2 pid1), witness<:share_t>)))) pid_set) pid0)).`2.`1))
     GateFunctionality.pid_set) = (map
     (fun (pid0 : GateFunctionality.pid_t) =>
        (pid0, oget
                          (assoc
                             (eval_gates gg
                                r{2} D_WP.xs{2}).`2 pid0)))
     GateFunctionality.pid_set).
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.
rewrite (eq_assoc_map r{2}).
smt(pid_set_uniq).
congr.
congr.
congr.
congr.
have ->: (unzip1 r{2}) = pid_set by smt().
rewrite -eq_in_map; progress.
by rewrite /rand !map_assoc //=.

move : (correct_eval_gates (np,ns,m,q) gg r{2} D_WP.xs{2} ((oget (assoc D_WP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
   map SecretSharingScheme.reconstruct
     (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_WP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
have ->: (ArithmeticCircuit.Circuit.valid_topology (np,ns,m,q)) by smt().
have ->: (ArithmeticCircuit.valid_gates ((np,ns,m,q), gg)) by smt().
have ->: all
   (fun (pid : pid_t) => gates_valid_rand gg (oget (assoc r{2} pid))) pid_set.
rewrite allP; progress.
move : H4; rewrite /valid_rands /=.
progress.
move : (H11 x2).
rewrite H10.
by rewrite /valid_rand /=.
have ->: valid_inputs_topology (np,ns,m,q) D_WP.xs{2} by smt().


have ->: pinput_finput_valid
   (((np,ns,m,q), witness), D_WP.xs{2},
    ((oget (assoc D_WP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
     map SecretSharingScheme.reconstruct
       (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_WP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite /pinput_finput_valid /=.
rewrite !size_map.
move : H2.
rewrite /valid_inputs /= /valid_inputs_topology /= /pinput /sinput /input /=.
progress.
by rewrite H11; first by smt(pid_set_size n_pos).
by rewrite size_range /max => /#.
by rewrite H11; first by smt(pid_set_size n_pos).
by rewrite H12; first by smt(pid_set_size n_pos).
rewrite !map_assoc //=.
rewrite /pinput /input /=.
move : (H14 k); rewrite H16 H17 /=.
progress.
move : H19; rewrite allP; progress.
have : (pid0, nth witness (oget (assoc D_WP.xs{2} pid0)).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_WP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
by exists pid0 => /=.
have : ((head witness SecretSharingScheme.pid_set), nth witness (oget (assoc D_WP.xs{2} (head witness SecretSharingScheme.pid_set))).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_WP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
exists (head witness SecretSharingScheme.pid_set) => /=.
smt(pid_set_size n_pos).
smt().

rewrite -!map_comp /(\o) /=.
rewrite (nth_map witness).
by rewrite size_range => /#.
simplify.
rewrite /reconstruct.
congr.
rewrite -eq_in_map => pid'; progress.
rewrite nth_range 1:/#.
simplify.
rewrite /input.
done.

simplify.
rewrite /pgates_fgates_valid /=.
progress.
(*rewrite (eq_assoc_map ys0).
smt(pid_set_uniq).
congr.
have ->: (unzip1 ys0) = pid_set by smt().
rewrite -eq_in_map; progress.
smt().*)
(*rewrite !map_assoc //=.*)
rewrite /pinput /input /=.
move : H0 H. rewrite /eval_circuit -H11 /=.
progress.
move : H; rewrite -H0 /=.
progress.
rewrite (eq_assoc_map ys0). smt(pid_set_uniq).
have ->: (unzip1 ys0) = pid_set by smt(correct_domain).
congr.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.

move : H0 H. rewrite /eval_circuit /=.
progress.
move : H; rewrite -H0 /=.
progress.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
have ->: (map (fun (pid0 : pid_t) => (pid0, (ArithP.rand pid0 r{2}))) pid_set) = r{2}.
rewrite (eq_assoc_map r{2}). smt(pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
by rewrite /rand !map_assoc //=.
smt().

congr.
congr.
congr.
congr.
congr.
rewrite (eq_assoc_map rsp{2}). smt(pid_set_uniq).
have ->: (unzip1 rsp{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
by rewrite /rand !map_assoc //=.

rewrite -eq_in_map; progress.
rewrite /rand !map_assoc //=; first by smt().
move : (local_output_correct_gates (np,ns,m,q) gg x1 D_WP.xs{2} r{2}).
have ->: x1 \in pid_set by smt().
simplify.
have ->: (map (fun (pid2 : pid_t) => (pid2, (rand pid2 r{2})%ArithP))
                                  ProtocolFunctionality.pid_set) = r{2}.
rewrite eq_assoc_map; first by smt(pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
by rewrite /rand -eq_in_map; progress; rewrite !map_assoc //=.
rewrite /input /rand.
move : H0; rewrite -H /=.
progress.
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
smt().

rewrite -eq_in_map; progress.
move : H0; rewrite -H /=.
progress.

move : (correct_eval_gates (np,ns,m,q) gg r{2} D_WP.xs{2} ((oget (assoc D_WP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
   map SecretSharingScheme.reconstruct
     (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_WP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
have ->: (ArithmeticCircuit.Circuit.valid_topology (np,ns,m,q)) by smt().
have ->: (ArithmeticCircuit.valid_gates ((np,ns,m,q), gg)) by smt().
have ->: all
   (fun (pid : pid_t) => gates_valid_rand gg (oget (assoc r{2} pid))) pid_set.
rewrite allP; progress.
move : H4; rewrite /valid_rands /=.
progress.
move : (H10 x2).
rewrite H0.
by rewrite /valid_rand /=.
have ->: valid_inputs_topology (np,ns,m,q) D_WP.xs{2} by smt().


have ->: pinput_finput_valid
   (((np,ns,m,q), witness), D_WP.xs{2},
    ((oget (assoc D_WP.xs{2} (head witness SecretSharingScheme.pid_set))).`1,
     map SecretSharingScheme.reconstruct
       (map
        (fun (k : int) =>
           map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc D_WP.xs{2} pid0)).`2 k))
             SecretSharingScheme.pid_set) (range 0 (np+ns))))).
rewrite /pinput_finput_valid /=.
rewrite !size_map.
move : H2.
rewrite /valid_inputs /= /valid_inputs_topology /= /pinput /sinput /input /=.
progress.
by rewrite H10; first by smt(pid_set_size n_pos).
by rewrite size_range /max => /#.
by rewrite H10; first by smt(pid_set_size n_pos).
by rewrite H11; first by smt(pid_set_size n_pos).
rewrite !map_assoc //=.
rewrite /pinput /input /=.
move : (H13 k); rewrite H15 H16 /=.
progress.
move : H18; rewrite allP; progress.
have : (pid0, nth witness (oget (assoc D_WP.xs{2} pid0)).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_WP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
by exists pid0 => /=.
have : ((head witness SecretSharingScheme.pid_set), nth witness (oget (assoc D_WP.xs{2} (head witness SecretSharingScheme.pid_set))).`1 k) \in map (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc D_WP.xs{2} pid1)).`1 k))
         SecretSharingScheme.pid_set.
rewrite mapP.
progress.
exists (head witness SecretSharingScheme.pid_set) => /=.
smt(pid_set_size n_pos).
smt().

rewrite -!map_comp /(\o) /=.
rewrite (nth_map witness).
by rewrite size_range => /#.
simplify.
rewrite /reconstruct.
congr.
rewrite -eq_in_map => pid'; progress.
rewrite nth_range 1:/#.
simplify.
rewrite /input.
done.

simplify.
rewrite /pgates_fgates_valid /=.
progress.
have ->: (map (fun (pid1 : pid_t) => (pid1, (rand pid1 r{2})%ArithP)) ProtocolFunctionality.pid_set) = r{2}.
rewrite (eq_assoc_map r{2}). smt(pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
by rewrite /rand !map_assoc //=.
rewrite /f /=.
rewrite !map_assoc //=; first 2 by smt().
rewrite /pinput /sinput /input /= /eval_circuit -H10 /=.
rewrite (eq_assoc_map ((eval_gates gg r{2} D_WP.xs{2}).`2)).
smt(pid_set_uniq).
have ->: unzip1 (eval_gates gg r{2} D_WP.xs{2}).`2 = pid_set.
smt().
congr.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.
by rewrite !map_assoc //=.
    qed.

    lemma weak_equiv_ideal :
      equiv [ Privacy.GameIdeal(D, R_PP(R_WP, R_SP), Simulator).main ~ WP_S.GameIdeal(D_WP(D, R_SP), R_WP).main :
                ={c,x,aux} /\ ={glob D, glob R_SP, glob R_WP} ==> ={res} ].
    proof.
      proc; inline*; sp.
      seq 1 1 : (#pre /\ xs{1} = D_WP.xs{2} /\ cr{1} = D_WP.cr{2}); first
        by call (_ : true); skip => /#. 
      sp; seq 1 1 : (#pre /\ rwp{1} = r{2}); first 
        by call (_ : true); skip => /#. 
      if{2}; last first.
      rcondf{1} 5; first move => &m; wp; call (_ : true); wp; skip; progress.
        move : H.
        rewrite /valid_inputs /= /pid_set /= /valid_corrupted_set /= /sum_topo /= /t /= 
                /pid_set /= /valid_rands /= -!map_comp /(\o) /= map_id /= /pid_set /=; progress.

        case (forall (pid : pid_t), pid \in pid_set => ArithP.valid_rand c{m} (oget (assoc (map (fun (pid0 : pid_t) => (pid0, oget (assoc r{m} pid0))) pid_set) pid))); last first.
          progress.
          have ->: ! (forall (pid : ProtocolFunctionality.pid_t), pid \in pid_set => valid_rand c{m} (oget (assoc (map (fun (pid0 : ArithP.ProtocolFunctionality.pid_t) => (pid0, ((rand pid0 r{m})%ArithP, rand pid0 result))) pid_set) pid))).
            move : H2; rewrite !neg_forall; progress; exists x1.
            case (x1 \in pid_set); progress; last by smt().
              rewrite /rand !map_assoc //= /rand; move : H2.
              by rewrite H3 /rand !map_assoc //= /valid_rand /= => /#.
          by smt().
          by smt().
          rewrite /valid_rands /=; have ->: [] = pid_set <=> false.
            smt(pid_set_size n_pos).
          done.
        by rnd; wp; call{1} r_sp_gen_ll; wp; skip. 
      sp; seq 1 1 : (#pre /\ ={rsp}); first by call (_ : true); skip; progress.
      sp 1 0; if => //; last first.
      rcondf{1} 2; first move => &m; wp; skip; progress.
          rewrite /valid_rands /=; have ->: [] = pid_set <=> false.
            smt(pid_set_size n_pos).
          done.
        by wp; rnd; wp.
        progress.
      rcondt{1} 3; first move => &m; wp; skip; progress.
smt().
smt().
smt().
by rewrite -!map_comp /(\o) /= map_id //=. 
        * move : H1; rewrite /valid_rands /=; progress.
          move : (H6 pid); rewrite H5 /= /rand !map_assoc //= /rand //= /valid_rand /=; progress.
          smt().
          move : H4; rewrite /valid_rands /=; progress.
          by move : (H8 pid); rewrite H5 /= /rand /#. 
        * by smt().
        * by smt().
      wp; call (_ : true); wp; skip; progress.
      rewrite -eq_in_map => pid H6 /=.
      rewrite /input /rand /output /trace /view.
      rewrite /protocol /= /eval_circuit. 
progress.
rewrite /extract_inputs.
by rewrite !map_assoc //=.

      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ArithP.ProtocolFunctionality.pid_t) => (pid1, (oget (assoc r{2} pid1), oget (assoc rsp{2} pid1)))) pid_set) pid0)).`1)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, ArithP.rand pid r{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc //= !map_assoc //=.
have ->: (map (fun (pid0 : pid_t) => (pid0, (rand pid0 r{2})%ArithP)) ProtocolFunctionality.pid_set) = r{2}.
rewrite eq_assoc_map; first by smt(pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
rewrite /rand !map_assoc //=.
move : H; rewrite /extract_inputs /input.
smt().

congr.
congr.
congr.
congr.
rewrite (eq_assoc_map rsp{2}); first by smt(correct_domain pid_set_uniq).
have ->: (unzip1 rsp{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
rewrite /rand !map_assoc //=.
by rewrite /rand !map_assoc //=.
rewrite -eq_in_map; progress.
move : H H0 H1 H3.
elim (c{2}) => topo gg /=.
elim topo => np ns m q /=.
progress.
move : (local_output_correct_gates (np,ns,m,q) gg x1 D_WP.xs{2} (map (fun (pid0 : pid_t) => (pid0, (rand pid0 r{2})%ArithP)) ProtocolFunctionality.pid_set)).
have ->: x1 \in pid_set by smt().
simplify.
rewrite /rand /input.
rewrite !map_assoc //=; first by smt().
have ->: (map (fun (pid0 : pid_t) => (pid0, oget (assoc r{2} pid0))) ProtocolFunctionality.pid_set) = r{2}.
rewrite (eq_assoc_map); first by smt(correct_domain pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.
      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ArithP.ProtocolFunctionality.pid_t) => (pid1, (oget (assoc r{2} pid1), oget (assoc rsp{2} pid1)))) pid_set) pid0)).`1)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, ArithP.rand pid r{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc //= !map_assoc //=.
have ->: (map (fun (pid0 : pid_t) => (pid0, (rand pid0 r{2})%ArithP)) ProtocolFunctionality.pid_set) = r{2}.
rewrite eq_assoc_map; first by smt(pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
rewrite /rand !map_assoc //=.
move : H; rewrite /extract_inputs /input.
smt().
      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ArithP.ProtocolFunctionality.pid_t) => (pid1, (oget (assoc r{2} pid1), oget (assoc rsp{2} pid1)))) pid_set) pid0)).`1)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, ArithP.rand pid r{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc //= !map_assoc //=.
have ->: (map (fun (pid0 : pid_t) => (pid0, (rand pid0 r{2})%ArithP)) ProtocolFunctionality.pid_set) = r{2}.
rewrite eq_assoc_map; first by smt(pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
by rewrite /rand !map_assoc //=.

      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ArithP.ProtocolFunctionality.pid_t) => (pid1, (oget (assoc r{2} pid1), oget (assoc rsp{2} pid1)))) pid_set) pid0)).`2)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, oget(assoc rsp{2} pid))) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc //= !map_assoc //=.
have ->: (map (fun (pid0 : pid_t) => (pid0, oget (assoc rsp{2} pid0))) ProtocolFunctionality.pid_set) = rsp{2}.
rewrite eq_assoc_map; first by smt(pid_set_uniq).
have ->: (unzip1 rsp{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
by rewrite /rand !map_assoc //=.

congr.
congr.
congr.
congr.
congr.
rewrite -eq_in_map; progress.
move : H; rewrite /extract_inputs /= /input /=.
smt().

      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ArithP.ProtocolFunctionality.pid_t) => (pid1, (oget (assoc r{2} pid1), oget (assoc rsp{2} pid1)))) pid_set) pid0)).`1)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, ArithP.rand pid r{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc //= !map_assoc //=.
have ->: (map (fun (pid0 : pid_t) => (pid0, (rand pid0 r{2})%ArithP)) ProtocolFunctionality.pid_set) = r{2}.
rewrite eq_assoc_map; first by smt(pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
rewrite /rand !map_assoc //=.
move : H; rewrite /extract_inputs /input.
smt().
      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ArithP.ProtocolFunctionality.pid_t) => (pid1, (oget (assoc r{2} pid1), oget (assoc rsp{2} pid1)))) pid_set) pid0)).`1)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, ArithP.rand pid r{2})) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc //= !map_assoc //=.
have ->: (map (fun (pid0 : pid_t) => (pid0, (rand pid0 r{2})%ArithP)) ProtocolFunctionality.pid_set) = r{2}.
rewrite eq_assoc_map; first by smt(pid_set_uniq).
have ->: (unzip1 r{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
rewrite /rand !map_assoc //=.
      have ->: (map (fun (pid0 : ProtocolFunctionality.pid_t) => (pid0, (oget (assoc (map (fun (pid1 : ArithP.ProtocolFunctionality.pid_t) => (pid1, (oget (assoc r{2} pid1), oget (assoc rsp{2} pid1)))) pid_set) pid0)).`2)) ProtocolFunctionality.pid_set) = (map (fun (pid : pid_t) => (pid, oget(assoc rsp{2} pid))) ProtocolFunctionality.pid_set)
        by rewrite -eq_in_map => pid'; progress; rewrite !map_assoc //= !map_assoc //=.
have ->: (map (fun (pid0 : pid_t) => (pid0, oget (assoc rsp{2} pid0))) ProtocolFunctionality.pid_set) = rsp{2}.
rewrite eq_assoc_map; first by smt(pid_set_uniq).
have ->: (unzip1 rsp{2}) = pid_set by smt(correct_domain).
rewrite -eq_in_map; progress.
by rewrite /rand !map_assoc //=.

congr.
congr.
congr.
congr.
congr.
rewrite -eq_in_map; progress.
move : H; rewrite /extract_inputs /= /input /=.
smt().
qed.


    local lemma adv_weak_hop &m c x aux : 
      Pr[Game1.main(c,x,aux) @ &m : res] -
      Pr[Privacy.GameIdeal(D, R_PP(R_WP, R_SP), Simulator).main(c,x,aux) @ &m : res]
       <=
      Pr[WP_S.GameReal(D_WP(D, R_SP), R_WP).main(c,x,aux) @ &m : res] -
      Pr[WP_S.GameIdeal(D_WP(D, R_SP), R_WP).main(c,x,aux) @ &m : res].
    proof.
      have ->: Pr[Game1.main(c,x,aux) @ &m : res] =
              Pr[WP_S.GameReal(D_WP(D, R_SP), R_WP).main(c,x,aux) @ &m : res]
        by byequiv weak_equiv_real => /#.
      have ->: Pr[Privacy.GameIdeal(D, R_PP(R_WP, R_SP), Simulator).main(c,x,aux) @ &m : res] = 
               Pr[WP_S.GameIdeal(D_WP(D, R_SP), R_WP).main(c,x,aux) @ &m : res]
        by byequiv weak_equiv_ideal => /= /#.
      by done.
    qed.

    local lemma adv_composition &m c x aux : 
      Pr[Privacy.GameReal(D, R_PP(R_WP, R_SP)).main(c,x,aux) @ &m : res] -
      Pr[Privacy.GameIdeal(D, R_PP(R_WP, R_SP), Simulator).main(c,x,aux) @ &m : res]
       <=
      Pr[SP_S.GameReal(D_SP(D, R_WP), R_SP).main(x,(aux,c)) @ &m : res] -
      Pr[SP_S.GameIdeal(D_SP(D, R_WP), R_SP).main(x,(aux,c)) @ &m : res] +
      Pr[WP_S.GameReal(D_WP(D, R_SP), R_WP).main(c,x,aux) @ &m : res] -
      Pr[WP_S.GameIdeal(D_WP(D, R_SP), R_WP).main(c,x,aux) @ &m : res].
    proof.
      move : (adv_strong_hop &m c x aux).
      move : (adv_weak_hop &m c x aux).
      by smt().
    qed.

  end section Proof.

end WeakPrivacyComposition.
