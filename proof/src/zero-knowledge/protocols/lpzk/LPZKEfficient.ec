(**
  Memory-based optimization step: replacing the usage of lists by arrays (**LPZKFasterArray**). 

  The EasyCrypt proof assistant was not originally developed to provide implementations to be 
  executed, but rather to provide models to reason about. For instance, in cryptographic proofs, 
  it is common practice to use lists to store security sensitive information, such as messages 
  exchanged during a protocol. This leads to formalizations that will also resort to lists as the
  main memory data structure. However, the use of lists therein, while convenient for the 
  development of machine-checked security proofs, hinders the efficiency of the extracted code. 
  In this file, we explore how changing the memory data structure to one with constant-time 
  access, such as arrays, affects the performance of the extracted code.

  Technically, the EasyCrypt formalization of the array-based LPZK is obtained by replacing all 
  occurrences of the **list** type by the newly defined **array** type and all occurrences of 
  **nth** (the **list** access EasyCrypt operator) by the **get** array operator. To prove that
  the array-based LPZK implementation achieves the same security level as the list-based LPZK,
  we need to follow a similar approach to what was followed in the *LPZKFaster.ec* script.
  Essentially, we need to prove that taking inputs and randomness stored as arrays, and
  accessed via the **get** array operator, doesn't affect the commitment message sent by the
  prover to the verifier and that final output of the protocol is the same as in the list-based
  version. Because we are only modifying the types of the protocol inputs (and not the type of
  the message) our task is slightly simpler, as we will only need to establish an isomorphism
  between the two versions at the input level.

  Completeness, soundness and zero knowledge for this new version of LPZK were derived by proving
  that both the list-based and array-based versions have the same observable behavior. 
  Informally, we prove that a prover using the array-based LPZK will produce the same commitment
  as a prover using the list-based LPZK, and that the verifier decision is independent from how
  the commitment is calculated (either via list-based LPZK or via array-based LPZK). Armed with
  these two properties, we prove that: 
    i. the completeness game of the array-based LPZK version has the same probability of the 
       completeness game of the list-based LPZK version; 
    ii. the soundness game of the array-based LPZK version has the same probability of the 
        soundness game of the list-based LPZK version; and 
    iii. that the real zero knowledge game of the array-based LPZK version is indistinguishable 
         from the real game of the list-based LPZK version and, therefore, the same simulator 
         can be used to prove zero knowledge.
*)
require import Int Real List.

from DVNIZK require import ADVNIZKProtocol.
from DVNIZK require import DVNIZKCompleteness DVNIZKSoundness DVNIZKZeroKnowledge.
from Zarith require import PrimeField.

from Utilities require import Array.

from LPZK require import LPZK LPZKFaster.

import LPZK.
import ArithmeticCircuit.
import Circuit.
import LPZKFaster.

theory LPZKEfficient.

  (** The witness is an array of finite field values *)
  type witness_t = t array.
  (** The instance is an array of finite field values *)
  type instance_t = t array.
  (** The statement is the combination of the circuit with the instance *)
  type statement_t = circuit_t * instance_t.

  (** Without loss of generality, we will only consider arithmetic circuits that evaluate to 0,
      meaning that a proof is considered valid if it is modeled by an arithmetic circuit that
      evaluates to 0.

      [eval_circuit_array] is equivalent to [eval_circuit], but takes its inputs as arrays 
      instead of lists *)
  op relation (w : witness_t) (x : statement_t) : bool = 
    let (c, inst) = x in
    eval_circuit_array c inst w = fzero.

  (** Prover input type. The prover starts the protocol holding the witness and the statement *)
  type prover_input_t = witness_t * statement_t.
  (** Verifier input type. The verifier starts the protocol holding the statement *)
  type verifier_input_t = statement_t.
  (** Input validity predicate. We consider an input to be *well-formed* if both parties hold
      the same statement (circuit and instance), if the circuit is valid and if the number
      of private and public inputs is in accordance with the circuit topology *)
  op valid_inputs (x : prover_input_t * verifier_input_t) : bool =
    let (xp, xv) = x in
    let (w, stp) = xp in
    let (c, inst) = xv in
    let topo = c.`topo in
    let gg = c.`gates in
    stp = xv /\ valid_circuit c /\ size w = topo.`nsinputs /\ size inst = topo.`npinputs.

  (** Prover randomness specification *)
  (** The prover will have an array composed of four field elements (a, b, a' and b') per gate *)
  type ui_t = LPZK.ui_t.
  (** Default value for an element of the prover randomness *)
  op def_ui : ui_t = LPZK.def_ui.
  (** The type of arrays of elements of type [ui_t] *)
  type u_t = ui_t array.
  (** The prover randomness is an array of elements of type [ui_t] *)
  type prover_rand_t = u_t.

  (** Randomness validity predicate for the prover. We consider the prover randomness to be valid
      if it has the correct number of elements and if the last [a] element of the prover 
      randomness is different than 0 *)
print LPZK.valid_rand_prover.

  op valid_rand_prover (r : prover_rand_t) (x : statement_t) : bool =
    let (c, inst) = x in
    let topo = c.`topo in
    let gg = c.`gates in
    size r = topo.`nsinputs + topo.`npinputs + topo.`ngates + 2 /\
    forall (k : int), 0 <= k && k < size r => (get def_ui r k).`a <> fzero.

  (** Verifier randomness specification *)
  (** The verifier will have an array composed of two field elements (v and v') per gate *)
  type yi_t = LPZK.yi_t.
  (** Default value for an element of the verifier randomness *)
  op def_yi : yi_t = LPZK.def_yi.
  (** The type of arrays of elements of type [yi_t] *)
  type y_t = yi_t array.
  (** The verifier randomness is a finite field element and an array of elements of type [yi_t] *)
  type verifier_rand_t = { alpha : t ; y : y_t }.

  (** Randomness validity predicate for the verifier. We consider the verifier randomness to be 
      valid if it has the correct number of elements and if the verifier and prover randomness
      are correlated with respect to an affine function that evaluates to 𝛼 *) 
  op valid_rand_verifier (rp : prover_rand_t) (rv : verifier_rand_t) (x : verifier_input_t) : bool =
    let alpha = rv.`alpha in let y = rv.`y in
    size y = size rp /\
    (forall k, 0 <= k < size y => 
      (get def_yi y k).`v = fadd (fmul alpha (get def_ui rp k).`a) (get def_ui rp k).`b) /\
    (forall k, 0 <= k < size y => 
      (get def_yi y k).`v' = fadd (fmul alpha (get def_ui rp k).`a') (get def_ui rp k).`b').

  (** Prover output type. At the end of the protocol, the prover has no output *)
  type prover_output_t = unit. 
  (** Verifier output type. At the end of the protocol, the verifier outputs a boolean, stating
      if it accepts the proof or not *)
  type verifier_output_t = bool.

  (** The [z] data structure is the same as in **LPZK** *)
  type z_t = LPZK.z_t.

  (** Generates the [z] data structure based on the prover algorithm, taking inputs and 
      randomness stored in arrays *)
print gen_z.

  op gen_z (u : prover_rand_t) (gg : gates_t) (xp : t array) (xs : t array) : z_t =
    with gg = PInput wid => 
      let b = (get def_ui u wid).`b in
      let w = eval_gates_array gg xp xs in
      PInputZ wid {| m = fsub w b |}

    with gg = SInput wid => 
      let b = (get def_ui u wid).`b in
      let w = eval_gates_array gg xp xs in
      SInputZ wid {| m = fsub w b |}

    with gg = Constant gid c => 
      let b = (get def_ui u gid).`b in
      let w = eval_gates_array gg xp xs in
      ConstantZ gid {| m = fsub w b |}

    with gg = Addition gid wl wr =>
      let b = (get LPZK.def_ui u gid).`b in  
      let w = eval_gates_array gg xp xs in
      AdditionZ gid {| m = fsub w b |} (gen_z u wl xp xs) (gen_z u wr xp xs)

    with gg = Multiplication gid l r => 
      let wl = eval_gates_array l xp xs in
      let wr = eval_gates_array r xp xs in
      let w = fmul wl wr in
      let ui = get LPZK.def_ui u gid in
      let a = ui.`a in
      let b = ui.`b in
      let a' = ui.`a' in
      let b' = ui.`b' in
      let ul = get LPZK.def_ui u (get_gid l)
      in
      let al = ul.`LPZK.a in
      let bl = ul.`LPZK.b in
      let a'l = ul.`LPZK.a' in
      let b'l = ul.`LPZK.b' in
      let ur = get LPZK.def_ui u (get_gid r)
      in
      let ar = ur.`LPZK.a in
      let br = ur.`LPZK.b in
      let a'r = ur.`LPZK.a' in
      let b'r = ur.`LPZK.b' in
      MultiplicationZ gid {| m_mul = fsub w b; 
                             m' = fsub (fmul al ar) a'; 
                             c = fsub (fsub (fadd (fmul al wr) (fmul ar wl)) a) b'; |}
        (gen_z u l xp xs) (gen_z u r xp xs).

 (** Gets the random [a] value from the prover randomness, i.e., gets the [a] random value
      associated with the ouput circuit gate *)
  op get_a (u : prover_rand_t) (gg : gates_t) : t =
    let gid = get_gid gg in
    let ui = get def_ui u gid in
    ui.`a.

  (** The commitment is the same as in **LPZK** *)
  type commitment_t = LPZK.commitment_t.

  (** New [commit] function, equal to the [commit] function specified in *LPZK.ec*, but invokes
      the newly defined array-based [gen_z] operator *)
  op commit (r : prover_rand_t) (x : prover_input_t) : commitment_t = 
    let (w, st) = x in
    let (c, inst) = st in
    let c = add_final_mul c in
    let topo = c.`topo in
    let gg = c.`gates in
    
    let z = gen_z r gg inst w in
    let z' = (get_a r gg) in
    (z, z').

  (** The [f] data structure is the same as in **LPZK** *)
  type f_t = LPZK.f_t.

  (** The *bad* [f] value is the same as in **LPZKFaster** *)
  op bad : f_t = LPZKFaster.bad.

  (** Generates the [f] data structure based on the verifier algorithm, taking inputs and 
      randomness stored in arrays *)
  op gen_f (r : verifier_rand_t) (gg : gates_t) (z : z_t) : bool * f_t =
    with z = PInputZ wid zi => 
      if is_pinput gg then
        if as_pinput gg = wid then
          let m = zi.`m in
          let v = (get def_yi r.`y wid).`v in
          (true, PInputF {| e = fadd v m ; e' = fzero ; e'' = fzero |})
        else (false, bad)
      else (false, bad)

    with z = SInputZ wid zi => 
      if is_sinput gg then
        if as_sinput gg = wid then
          let m = zi.`m in
          let v = (get def_yi r.`y wid).`v in
          (true, SInputF {| e = fadd v m ; e' = fzero ; e'' = fzero |})
        else (false, bad)
      else (false, bad)

    with z = ConstantZ gid zi =>
      if is_constant gg then
        if (as_constant gg).`1 = gid then
          let m = zi.`m in
          let v = (get def_yi r.`y gid).`v in
          (true, ConstantF {| e = fadd v m ; e' = fzero ; e'' = fzero |})
        else (false, bad)
      else (false, bad)

    with z = AdditionZ gid zi zl zr =>
      if is_addition gg then
        let (gid', wl, wr) = as_addition gg in

        if gid = gid' then
          let (bl, fl) = gen_f r wl zl in
          let (br, fr) = gen_f r wr zr in
          let m = zi.`m in
          let v = (get def_yi r.`y gid).`v in
          if (bl /\ br) then
            (true, AdditionF {| e = fadd v m ; e' = fzero ; e'' = fzero |} fl fr)
          else (false, bad)
        else (false, bad)
      else (false, bad)

    with z = MultiplicationZ gid zi zl zr =>
      if is_multiplication gg then
        let (gid', wl, wr) = as_multiplication gg in

        if gid = gid' then
          let (bl, fl) = gen_f r wl zl in
          let (br, fr) = gen_f r wr zr in

          let m = zi.`m_mul in
          let m' = zi.`m' in

          let alpha = r.`alpha in
          let y = get def_yi r.`y gid in
          let v = y.`v in
          let v' = y.`v' in

          let el = get_e fl in
          let er = get_e fr in

          let e = fadd v m in
          let e' = fadd v' (fmul alpha m') in
          let e'' = fsub (fsub (fmul el er) e) (fmul alpha e') in

          if (bl /\ br) then
            (true, MultiplicationF {| e = e ; e' = e' ; e'' = e'' |} fl fr)
          else (false, bad)
        else (false, bad)
      else (false, bad).


  (** New [prove] function, equal to the [prove] function specified in *LPZK.ec*, but invokes
      the newly defined array-based [gen_f] operator *)
  op prove (r : verifier_rand_t) (x : verifier_input_t) (c : commitment_t) : bool =
    let (z, z') = c in
    let (circ, inst) = x in
    if (valid_circuit circ) then
      let circ = add_final_mul circ in
      let n = z' in
      if n <> fzero then
        let (b, f) = gen_f r circ.`gates z in
        if (b /\ batch_check f z r.`alpha) then
          get_e f = fmul n r.`alpha
        else false
      else false
    else false.

  (** The trace is the same as in **LPZK** *)
  type trace_t = LPZK.trace_t.

  (** Array-based [protocol] function, equal to the [protocol] function specified in *LPZK.ec*, 
      but invokes the array-based operators and takes inputs and random values stored in arrays
      instead of lists *)
  op protocol (r : prover_rand_t * verifier_rand_t) 
              (x : prover_input_t * verifier_input_t) : 
              trace_t * (prover_output_t * verifier_output_t) = 
    let (r_p, r_v) = r in let (x_p, x_v) = x in
    let c = commit r_p x_p in
    let b = prove r_v x_v c in (c, ((),b)).

  (** Proves that producing a commit using the list-based LPZK version, where inputs and 
      randomness are converted from an array to a list, produces the same commitment as 
      the array-based LPZK version

      This lemma together with the next one, establish an isomorphism between the list-based
      and array-based LPZK formalizations at the input level *)
  lemma commit_equivalence_faster (rp : prover_rand_t) (xp : prover_input_t) : 
    LPZKFaster.commit (to_list rp) (to_list xp.`1, (xp.`2.`1, to_list xp.`2.`2)) = commit rp xp.
  proof.
    rewrite /commit /= /add_final_mul /=.
    elim xp => wit st /=.
    elim st => c inst /=.
    elim c => topo gg /=.
    rewrite /LPZKEfficient.def_ui /LPZKEfficient.def_yi /LPZKEfficient.get_a /= 
            /LPZKEfficient.prove /=.
    progress. congr.
      by rewrite !eval_gates_array_eq nth_to_list.
      by rewrite !nth_to_list.
    elim gg => //.
      by move => wid; progress; rewrite !nth_to_list /=.
      by move => wid; progress; rewrite !nth_to_list /=.
      by move => gid c; progress; rewrite !nth_to_list /=.
      by move => gid l r; progress; rewrite !nth_to_list /= !eval_gates_array_eq => /#.
      by move => gid l r; progress; rewrite !nth_to_list /= !eval_gates_array_eq => /#.
    by rewrite /get_a /= !nth_to_list.
    elim gg => //.
      by move => wid; progress; rewrite !nth_to_list /=.
      by move => wid; progress; rewrite !nth_to_list /=.
      by move => gid c; progress; rewrite !nth_to_list /=.
      by move => gid l r; progress; rewrite !nth_to_list /= !eval_gates_array_eq => /#.
      by move => gid l r; progress; rewrite !nth_to_list /= !eval_gates_array_eq => /#.
    elim gg => //.
      by move => wid; progress; rewrite !nth_to_list /=.
      by move => wid; progress; rewrite !nth_to_list /=.
      by move => gid c; progress; rewrite !nth_to_list /=.
  qed.

  (** Proves that producing a commit using the array-based LPZK version, where inputs and 
      randomness are converted from a list to an array, produces the same commitment as 
      the list-based LPZK version

      This lemma together with the previous one, establish an isomorphism between the list-based
      and array-based LPZK formalizations at the input level *)
  lemma commit_equivalence_array rp xp : 
    LPZKFaster.commit rp xp = commit (of_list rp) (of_list xp.`1, (xp.`2.`1, of_list xp.`2.`2)).
  proof.
    rewrite /commit /= /add_final_mul /=.
    elim xp => wit st /=.
    elim st => c inst /=.
    elim c => topo gg /=.
    rewrite /LPZKEfficient.def_ui /LPZKEfficient.def_yi /LPZKEfficient.get_a /= 
            /LPZKEfficient.prove /=.
    progress. congr.
      by rewrite !eval_gates_list_eq get_of_list.
      by rewrite !get_of_list.
    elim gg => //.
      by move => wid; progress; rewrite !get_of_list /=.
      by move => wid; progress; rewrite !get_of_list /=.
      by move => gid c; progress; rewrite !get_of_list /=.
      by move => gid l r; progress; rewrite !get_of_list /= !eval_gates_list_eq => /#.
      by move => gid l r; progress; rewrite !get_of_list /= !eval_gates_list_eq => /#.
    elim gg => //.
      by move => wid; progress; rewrite !get_of_list /=.
      by move => wid; progress; rewrite !get_of_list /=.
      by move => gid c; progress; rewrite !get_of_list /=.
    elim gg => //.
      by move => wid; progress; rewrite !get_of_list /=.
      by move => wid; progress; rewrite !get_of_list /=.
      by move => gid c; progress; rewrite !get_of_list /=.
      by move => gid l r; progress; rewrite !get_of_list /= !eval_gates_list_eq => /#.
      by move => gid l r; progress; rewrite !get_of_list /= !eval_gates_list_eq => /#.
    by rewrite /get_a /= !get_of_list.
  qed.

  (** Proves that generating [f] using the list-based LPZK version, where inputs and 
      randomness are converted from an array to a list, produces the same [f] as 
      the array-based LPZK version *)
  lemma gen_f_equivalence_faster (rv : verifier_rand_t) (gg : gates_t) (z : z_t) :
    LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) gg z = gen_f rv gg z.
  proof.

    elim: z gg => //=.
      by move => gid zi gg; progress; rewrite !nth_to_list /= /create_verifier_rand /=.
      by move => gid zi gg; progress; rewrite !nth_to_list /= /create_verifier_rand /=.
      by move => gid zi gg; progress; rewrite !nth_to_list /= /create_verifier_rand /=.
      move => gid zi zl zr; progress.
        case (is_addition gg); progress.
        have : exists gid' wl wr, gg = Addition gid' wl wr by
          exists (as_addition gg).`1 (as_addition gg).`2 (as_addition gg).`3 => /#.
        progress.
        rewrite /get_e; case (gid = gid'); progress.
        have : exists (bl, fl), (bl, fl) = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wl zl) by exists (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wl zl).`1 (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wl zl).`2 => /#.
        have : exists (br, fr), (br, fr) = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wr zr) by exists (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wr zr).`1 (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wr zr).`2 => /#.
        progress.
        rewrite -H2 -H3 /=.
        have : exists (bl0, fl0), (bl0, fl0) = gen_f rv wl zl by exists (gen_f rv wl zl).`1 (gen_f rv wl zl).`2 => /#.
        have : exists (br0, fr0), (br0, fr0) = gen_f rv wr zr by exists (gen_f rv wr zr).`1 (gen_f rv wr zr).`2 => /#.
        progress.
        rewrite -H4 -H5 /=.
        have ->: bl = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wl zl).`1 by smt().
        have ->: fl = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wl zl).`2 by smt().
        have ->: br = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wr zr).`1 by smt().
        have ->: fr = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wr zr).`2 by smt().
        have ->: bl0 = (gen_f rv wl zl).`1 by smt().
        have ->: fl0 = (gen_f rv wl zl).`2 by smt().
        have ->: br0 = (gen_f rv wr zr).`1 by smt().
        have ->: fr0 = (gen_f rv wr zr).`2 by smt().
        clear H2 H3 H4 H5.
        move : (H wl); progress.
        move : (H0 wr); progress.
        by rewrite H2 H3 /=; smt.
      move => gid zi zl zr; progress.
        case (is_multiplication gg); progress.
        have : exists gid' wl wr, gg = Multiplication gid' wl wr by
          exists (as_multiplication gg).`1 (as_multiplication gg).`2 (as_multiplication gg).`3 => /#.
        progress.
        rewrite /get_e; case (gid = gid'); progress.
        have : exists (bl, fl), (bl, fl) = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wl zl) by exists (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wl zl).`1 (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wl zl).`2 => /#.
        have : exists (br, fr), (br, fr) = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wr zr) by exists (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wr zr).`1 (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wr zr).`2 => /#.
        progress.
        rewrite -H2 -H3 /=.
        have : exists (bl0, fl0), (bl0, fl0) = gen_f rv wl zl by exists (gen_f rv wl zl).`1 (gen_f rv wl zl).`2 => /#.
        have : exists (br0, fr0), (br0, fr0) = gen_f rv wr zr by exists (gen_f rv wr zr).`1 (gen_f rv wr zr).`2 => /#.
        progress.
        rewrite -H4 -H5 /=.
        have ->: bl = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wl zl).`1 by smt().
        have ->: fl = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wl zl).`2 by smt().
        have ->: br = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wr zr).`1 by smt().
        have ->: fr = (LPZKFaster.gen_f (create_verifier_rand rv.`alpha (to_list rv.`y)) wr zr).`2 by smt().
        have ->: bl0 = (gen_f rv wl zl).`1 by smt().
        have ->: fl0 = (gen_f rv wl zl).`2 by smt().
        have ->: br0 = (gen_f rv wr zr).`1 by smt().
        have ->: fr0 = (gen_f rv wr zr).`2 by smt().
        clear H2 H3 H4 H5.
        move : (H wl); progress.
        move : (H0 wr); progress.
        rewrite H2 H3 /=.
        case ((gen_f rv wl zl).`1 /\ (gen_f rv wr zr).`1); last first; progress.
        by rewrite /LPZKEfficient.def_yi /= /def_yi /=; congr; smt(nth_to_list get_of_list).
    qed.

  (** Proves that the [prove] operator of *LPZK.ec* is equivalent to the array-based [prove] 
      operator defined here *)
    lemma prove_equivalence_faster (rv : verifier_rand_t) (topo : topology_t) 
                                   (gg : gates_t) ys (c : commitment_t) (inst : instance_t) :
      LPZKFaster.prove (create_verifier_rand rv.`alpha (to_list rv.`y)) (({| topo = topo ; gates = gg ; out_wires = ys |}, to_list inst)) c = 
      prove rv ({| topo = topo ; gates = gg ; out_wires = ys |}, inst) c.
    proof. by rewrite /prove /=; smt(gen_f_equivalence_faster). qed.

  (** Proves that the list-based LPZK formalization in file *LPZK.ec* is equivalent to the 
      array-based formalization provided here *)
  lemma protocol_equivalence_faster (rp : prover_rand_t) (rv : verifier_rand_t) 
                                    topo gg ys w inst : 
    LPZKFaster.DVNIZKProtocol.protocol (to_list rp, (create_verifier_rand rv.`alpha (to_list rv.`y))) ((to_list w, ({| topo = topo ; gates = gg ; out_wires = ys |}, to_list inst)), ({| topo = topo ; gates = gg ; out_wires = ys |}, to_list inst)) = 
    protocol (rp, rv) ((w, ({| topo = topo ; gates = gg ; out_wires = ys |}, inst)), ({| topo = topo ; gates = gg ; out_wires = ys |}, inst)).
  proof. by smt(prove_equivalence_faster commit_equivalence_faster). qed.

  (** Instantiation of the DVNIZK protocol syntax with the array-based LPZK types and operators *)
  clone import ADVNIZKProtocol.DVNIZKProtocol with
    type witness_t = witness_t,
    type statement_t = statement_t,
    type prover_input_t = prover_input_t,
    type verifier_input_t = verifier_input_t,
    type prover_rand_t = prover_rand_t,
    type commitment_t = commitment_t,
    type trace_t = trace_t,
    type verifier_rand_t = verifier_rand_t,
    type prover_output_t = prover_output_t,
    type verifier_output_t = verifier_output_t,
    op relation = relation,
    op valid_inputs = valid_inputs,
    op valid_rand_verifier = valid_rand_verifier,
    op valid_rand_prover = valid_rand_prover,
    op commit = commit,
    op prove = prove,
    op protocol = protocol
  proof *.
  (** Correctness lemma. Proves that the protocol securely evaluates the relation, i.e.:
        - if the witness and statement are not in the relation, then the protocol always outputs
          false; and
        - if the witness and statement are in the relation, then the protocol always outputs true

      Because the array-based LPZK version is equivalent to the list-basedLPZK version of 
      *LPZK.ec* and *LPZKFaster.ec*, we re-use the correcntess lemma already proved in *LPZK.ec*
      and *LPZKFaster.ec*. *)
  realize correct.
    rewrite /valid_inputs /=.
    move => r x.
    elim r => rp rv /=.
    elim x => xp xv /=.
    elim xp => w stp /=.
    elim xv => c inst /=.
    elim c => topo gg ys /=.
    progress.
    have ->: (DVNIZKProtocol.relation w ({| topo = topo ; gates = gg ; out_wires = ys |}, inst)) = LPZKFaster.DVNIZKProtocol.relation (to_list w) ({| topo = topo ; gates = gg ; out_wires = ys |}, to_list inst) by
      rewrite /relation /= /eval_circuit /eval_circuit_array /= eval_gates_list_eq; smt(of_listK).
    rewrite /DVNIZKProtocol.protocol -(protocol_equivalence_faster rp rv topo gg ys w inst) 
            LPZKFaster.DVNIZKProtocol.correct /valid_inputs //=; first by rewrite !size_to_list.
      move : H2.
      rewrite /valid_rands /= /valid_rand_prover /valid_rand_verifier /=; progress.
        by rewrite size_to_list.
        rewrite -nth_to_list H3. move : H8. rewrite size_to_list. smt(). done.
        by rewrite /create_verifier_rand /= !size_to_list.
        move : H8; rewrite /create_verifier_rand /= size_to_list /=; progress.
        by rewrite -!nth_to_list => /#.
        move : H8; rewrite /create_verifier_rand /= size_to_list /=; progress.
        by rewrite -!nth_to_list => /#.
  qed.

  (** Completeness proof *)
  (** First, we import the completeness security definition instantiated with LPZKFasterArray *)
  clone import Completeness as LZPKCompleteness with
    theory DVNIZKProtocol <- DVNIZKProtocol.

  section Completeness.

    (** Randomness generator declaration *)
    declare module R <: Rand_t.
    (** Assumes that the randomness generator always terminates *)
    axiom r_gen_ll : islossless R.gen.

    (** Proves the desired completness lemma, according to the completeness game of the
        *CompletenessDVNIZKP.ec* file: we prove that, if the witness and the statement are in the
        relation, then the LPZK protocol will always produce true. The proof is done by using
        the correctness proof above. 

        Note that we could prove that the completeness game from *LPZK.ec* is equivalent to the
        one formalized here, but, although it would be an easy proof to do, it would be more 
        complex than the one we provide bellow *)
    lemma completeness &m w_ x_ : relation w_ x_ => 
                                  Pr[Completeness(R).main(w_,x_) @ &m : res] = 1%r.
    proof.
      move => H; byphoare (_ : w_ = w /\ x = x_ ==> res) => //.
      proc.
      seq 1 : #pre => //.
        by call r_gen_ll.
        by wp; skip; progress; move : (correct (r_p{hr}, r_v{hr}) ((w{hr}, x{hr}), x{hr})) => /#.
        by hoare; call (_ : true).
      qed.

  end section Completeness.

  (** Soundness proof *)
  (** First, we import the soundness security definition instantiated with LPZKFasterArray *)
  clone import Soundness as LPZKSoundness with
    theory DVNIZKProtocol <- DVNIZKProtocol.

  section Soundness.

    (** Malicious prover declaration *)
    declare module MP <: LPZK.LPZKSoundness.MProver_t.

    (** Randomness generator wrapper, that uses the list-based verifier random generator of
        file *LPZK.ec* to generate randomness for the array-based LPZK version *)
    module RVA = {
      proc gen(rp : prover_rand_t) : verifier_rand_t = {
        var rv;

        rv <@ LPZK.RV.gen(to_list rp);
        return ({| alpha = rv.`alpha ; y = of_list rv.`y |});
      }
    }.

    (** Malicious prover wrapper, that uses the list-based malicious prover to build a malicious
        prover for the array-based LPZK version *)
    module MPA = {
      proc commit(rp : prover_rand_t, x : statement_t) : commitment_t = {
        var c;

        c <@ MP.commit(to_list rp, (x.`1, to_list x.`2));
        return c;
      }
    }.

    (** Establishes the equivalence between the soundness game of **LPZKFaster** and the soundness
        game of **LPZKFasterArray**. If both games are equivalent, then they will have the same
        soundness error, which was already proved in *LPZK.ec* *)
    lemma soundness_eq :
      equiv [ Soundness(RVA, MPA).main ~ LPZKFaster.LPZKFasterSoundness.Soundness(LPZK.RV, MP).main : 
              to_list rp{1} = rp{2} /\ (x{1}.`1, to_list x{1}.`2) = x{2} /\ 
              ={glob LPZK.RV, glob MP} ==> ={res} ].
    proof.
      proc.
      seq 1 1 : (#pre /\ ={c}).
        by inline*; wp; call (_ : true); wp; skip; progress.
      seq 1 1 : (#pre /\ rv{1} = {| alpha = rv{2}.`alpha ; y = of_list rv{2}.`y |}).
        by inline *; wp; rnd; wp; skip; progress.
      (if => //=; last by wp); progress.
        by move : H; rewrite /valid_rand_verifier /=; rewrite !size_of_list !size_to_list.
        move : H; rewrite /valid_rand_verifier /= !size_of_list !get_of_list.
        progress.
        move : (H2 k); rewrite H0 H1 /= /LPZKEfficient.def_yi /= /def_yi /= 
                               /LPZKEfficient.def_ui /= /def_ui /=.
        by progress; rewrite of_listK. 
        move : H; rewrite /valid_rand_verifier /= !size_of_list !get_of_list.
        progress.
        move : (H3 k); rewrite H0 H1 /= /LPZKEfficient.def_yi /= /def_yi /= 
                               /LPZKEfficient.def_ui /= /def_ui /=.
        by progress; rewrite of_listK. 
        by move : H; rewrite /valid_rand_verifier /=; rewrite !size_of_list !size_to_list.
        move : H H1.
        rewrite /valid_rand_verifier /= !size_of_list !size_to_list.
        progress. move : (H1 k).
        by rewrite H0 H3 /= !get_of_list /LPZKEfficient.def_yi /= /def_yi /= 
                   /LPZKEfficient.def_ui /= /def_ui /= !of_listK.
        move : H H1.
        rewrite /valid_rand_verifier /= !size_of_list !size_to_list.
        progress. move : (H2 k).
        by rewrite H0 H3 /= !get_of_list /LPZKEfficient.def_yi /= /def_yi /= 
                   /LPZKEfficient.def_ui /= /def_ui /= !of_listK.
      wp; skip; progress.
      case (LPZKFaster.DVNIZKProtocol.language (x{1}.`1, to_list x{1}.`2)); progress.
        have ->: language x{1}.
          move : H0.
          rewrite /language /=; progress.
          exists (of_list w); move : H0.
          rewrite /relation //=.
          elim (x{1}) => c inst //=.
          rewrite /eval_circuit /eval_circuit_array //=.
          by elim c => topo gg /=; smt.
        by done.
      have ->: !language x{1}.
        move : H0.
        rewrite /language /=; progress.
        have : forall w, !LPZKFaster.DVNIZKProtocol.relation w (x{1}.`1, to_list x{1}.`2) by smt().
        progress.
        have : forall w, !(relation w x{1})%DVNIZKProtocol. 
          progress.
          move : (H1 (to_list w)).
          rewrite /relation /=.
          elim (x{1}) => c inst /=.
          rewrite /eval_circuit /eval_circuit_array /=.
          by elim c => topo gg /=; smt.
        by smt().
      simplify.
      rewrite /DVNIZKProtocol.prove /LPZKFaster.DVNIZKProtocol.prove.
      by smt(prove_equivalence_faster @Array).
    qed.

    (** Since the two soundness games are equivalent, they will have the same soundness error *)
    lemma soundness &m (x_ : statement_t) rp_ :
                                 Pr [ Soundness(RVA, MPA).main(rp_, x_) @ &m : res ] <= 2%r / q%r.
    proof.
      have ->: Pr[Soundness(RVA, MPA).main(rp_, x_) @ &m : res] = 
               Pr[LPZKFaster.LPZKFasterSoundness.Soundness(LPZK.RV, MP).main(to_list rp_, (x_.`1, to_list x_.`2)) @ &m : res]
        by byequiv soundness_eq.
      by rewrite (LPZKFaster.soundness MP).
    qed.

  end section Soundness.

  (** Zero-knowledge proof *)
  (** First, we import the zero-knowledge security definition instantiated with LPZKFasterArray *)
  clone import DVNIZKZeroKnowledge.ZeroKnowledge as LPZKEfficientZeroKnowledge with
    theory DVNIZKProtocol <- DVNIZKProtocol.

  section ZeroKnowledge.

    (** Distinguisher wrapper, that uses the list-based distinguisher to build a distinguisher 
        for the array-based LPZK version *)
    module DArray (D : LPZKFaster.LPZKFasterZeroKnowledge.Distinguisher_t) = {
      proc init() : prover_input_t * verifier_input_t = {
        var xp, xv, w, stp, cp, instp, cv, instv;

        (xp, xv) <@ D.init();
        (w, stp) <- xp;
        (cp, instp) <- stp;
        (cv, instv) <- xv;
        return ((of_list w, (cp, of_list instp)), (cv, of_list instv));
      }
      proc guess(to : trace_t option) : bool = {
        var b;
    
        b <@ D.guess(to);
        return b;
      }
    }.

    (** Randomness generator wrapper, that uses the list-based prover random generator of
        file *LPZK.ec* to generate randomness for the array-based LPZK prover *)
    module RPArray = {
      proc gen (x : statement_t) : prover_rand_t = {
        var r, c, inst;
        
        (c, inst) <- x;
        r <@ RP.gen(((c, to_list inst)));

        return (of_list r);
      }
    }.

    (** Malicious verifier wrapper, that uses the list-based malicious verifier to build a 
        malicious verifier for the array-based LPZK version *)
    module MVArray (MV : LPZKFaster.LPZKFasterZeroKnowledge.MVerifier_t) = {
      proc prove(x : statement_t, c : commitment_t) : bool = {
        var b, circ, inst;

        (circ, inst) <- x;
        b <@ MV.prove((circ, to_list inst), c);
        return b;
      } 
    }.

    (** Distinguisher declaration *)
    declare module D <: LPZKFaster.LPZKFasterZeroKnowledge.Distinguisher_t{-RealEvaluator, -IdealEvaluator, -Simulator, -LPZKZeroKnowledge.IdealEvaluator, -LPZKZeroKnowledge.RealEvaluator, -LPZKFasterZeroKnowledge.IdealEvaluator, -LPZKFasterZeroKnowledge.RealEvaluator}.
    (** Malicious verifier declaration *)    
    declare module MV <: LPZKFaster.LPZKFasterZeroKnowledge.MVerifier_t{-D, -RealEvaluator, -Simulator, -LPZKZeroKnowledge.IdealEvaluator, -LPZKZeroKnowledge.RealEvaluator, -LPZKFasterZeroKnowledge.IdealEvaluator, -LPZKFasterZeroKnowledge.RealEvaluator}.

    (** Establishes the equivalence between the *real* world game of **LPZK** and the *real*
        world game of **LPZKFasterArray**. If both games are equivalent, then the *real* world of
        **LPZKFasterArray** will also be equivalent to the *ideal* world game of **LPZK** and,
        consequently, **LPZKFasterArray** behavior could also be simulated by the simulator 
        defined in *LPZK.ec*. 

        In contrast to what we did for **LPZKFaster**, we directly prove the equivalence based
        on the output probability distribution of both games *)    
    lemma zero_knowledge &m :
      Pr[ GameReal(DArray(D), RPArray, MVArray(MV)).main() @ &m : res ] = 
      Pr[ LPZK.LPZKZeroKnowledge.GameIdeal(D, MV, LPZK.Simulator).main() @ &m : res ].
    proof.
rewrite -(LPZKFaster.zero_knowledge D MV).
byequiv => //=.
proc; inline*.
conseq (_ : ={glob D, glob MV} ==> ).
done.
seq 1 1 : (#pre /\ xp0{1} = xp{2} /\ xv0{1} = xv{2}).
call (_ : true); skip; progress.
sp.
if => //=; last first.
wp; call (_ : true); wp; skip; progress.
rewrite /valid_inputs //=.
progress.
smt(@Array).
smt(@Array).
smt(@Array).
smt(@Array).
smt(@Array).
      sp 9 7 => /=.
      seq 3 3 : (#pre /\ rp0{1} = rp0{2}).
        case (topo{2}.`npinputs + topo{2}.`nsinputs + topo{2}.`ngates < 0).
          rcondf{1} 3. progress. wp; skip; progress. smt().
          rcondf{2} 3. progress. wp; skip; progress. smt().
          wp; skip; progress.
smt().
smt().
smt().
smt().

        while (#pre /\ ={i} /\ 0 <= i{2} <= topo{2}.`npinputs + topo{2}.`nsinputs + topo{2}.`ngates /\ rp0{1} = rp0{2}).
          wp.
          do rnd.
          wp; skip; progress.
            smt().
            smt().
smt().
smt().
smt().
smt().
smt().
smt().
          wp; skip; progress.
            smt().
smt().
smt().
smt().
smt().
smt().
smt().
      seq 12 11 : (#pre /\ rp{1} = of_list rp{2} /\ rp0{1} = rp0{2}).
       by  wp; do rnd; wp; do rnd; skip; progress; smt().
      if => //=; last first.
wp; call (_ : true); wp; skip; progress.

        progress.
          by move : H0; rewrite /valid_rand_prover /=; progress; smt(@Array).
          by move : H0; rewrite /valid_rand_prover /=; progress; smt(@Array).
          by move : H0; rewrite /valid_rand_prover /=; progress; smt(@Array).
          by move : H0; rewrite /valid_rand_prover /=; progress; smt(@Array).
      wp; call (_ : true); wp; call (_ : true); wp; skip; progress. 
        by move : H0; rewrite /valid_rand_prover /=; progress; smt(@Array).
        by smt.       
    qed.      

  end section ZeroKnowledge.

  (** Final printouts, printing a *readable* version of the completeness, soundness and 
      zero-knowledge lemmas *)
  print completeness.
  print soundness.
  print zero_knowledge.

end LPZKEfficient.
