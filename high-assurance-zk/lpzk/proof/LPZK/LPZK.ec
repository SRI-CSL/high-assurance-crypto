(**
  Formalization of the LPZK protocol. Our LPZK specification instantiates the syntax defined for
  designated verifier non-interactive zero-knowledge protocols (DVNIZK) defined in the
  *ADVNIZKP.ec* file. The LPZK protocol is briefly describe bellow, by means of a dealer, prover
  and verifier algorithms. The dealer is an ideal functionality replaced by a VOLE protocol in 
  the actual executon of the protocol. As is going to be made clear in this formalization, we
  will formalize the dealer as (honest) random generator modules, and we will axiomatize the
  correlation property.

  Dealer algorithm: 𝛼, u = (a, a', b, b'); y = (v, v'), where
    Input wires: u = ($a, $b, ⊥, ⊥); y = (a𝛼 + b, ⊥)
    Add   wires: u = (a_l + a_r, b_l + b_r, ⊥, ⊥); y = (a𝛼 + b, ⊥)
    Mul   wires: u = ($a, $b, $a', $b'); y = (a𝛼 + b, a'𝛼 + b')

  Prover algorithm: z = (m, m', c), where
    Input wires: z = (w - b, ⊥, ⊥)
    Add   wires: z = (⊥, ⊥, ⊥)
    Mul   wires: z = (w - b, a_l * a_r - a', a_l * w_r + a_r * w_l - a - b')
  Final message: (z, (a, c_i * c_j * ...))

  Verifier algorithm: f = (e, e', e''), where
    Input wires: f = (v + w, ⊥, ⊥)
    Add   wires: f = (e_l + e_r, ⊥, ⊥)
    Mul   wires: f = (v + w, v' + 𝛼m', e_l * e_r - e - 𝛼e')
  Check: Output wire: e == n*𝛼 + w
         Batched checks: e_i'' * e_j'' == n𝛼^2

  A more formal and comprehensive description of the LPZK protocol can be found at the following
  papers:
    - Samuel Dittmer, Yuval Ishai, and Rafail Ostrovsky. *Line-Point Zero Knowledge and Its 
      Applications*. Cryptology ePrint Archive, Paper 2020/1446. 
      https://eprint.iacr.org/2020/1446
    - Samuel Dittmer, Yuval Ishai, Steve Lu, and Rafail Ostrovsky. *Improving Line-Point Zero 
      Knowledge: Two Multiplications for the Price of One*. In Proceedings of the 2022 ACM SIGSAC
      Conference on Computer and Communications Security, CCS 2022, Los Angeles, CA, USA.
*)
require import Int Real List Distr DList Dexcepted.

from DVNIZK require import ADVNIZKProtocol.
from DVNIZK require import DVNIZKCompleteness DVNIZKSoundness DVNIZKZeroKnowledge.
from Zarith require import PrimeField.

from ArithmeticCircuit require import ArithmeticCircuit.

from Utilities require import ListExt.

theory LPZK.

  (** The LPZK protocol is defined over arithmetic circuits over finite fields *)
  clone import ArithmeticCircuit.
  import Circuit.

  (** The witness is a list of finite field values *)
  type witness_t = t list.
  (** The instance is a list of finite field values *)
  type instance_t = t list.
  (** The statement is the combination of the circuit with the instance *)
  type statement_t = circuit_t * instance_t.

  (** Without loss of generality, we will only consider arithmetic circuits that evaluate to 0,
      meaning that a proof is considered valid if it is modeled by an arithmetic circuit that
      evaluates to 0 *)
  op relation (w : witness_t) (x : statement_t) : bool =
    let (c, inst) = x in
    eval_circuit c inst w = fzero.

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
  (** The prover will have a list composed of four field elements (a, b, a' and b') per gate *)
  type ui_t = { a : t ; b : t ; a' : t ; b' : t }.
  (** Default value for an element of the prover randomness *)
  op def_ui : ui_t = {| a = fzero ; b = fzero ; a' = fzero ; b' = fzero |}.
  (** The type of lists of elements of type [ui_t] *)
  type u_t = ui_t list.
  (** The prover randomness is a list of elements of type [ui_t] *)
  type prover_rand_t = u_t.

  op add_final_mul (c : circuit_t) : circuit_t =
    let topo = c.`topo in
    let gg = c.`gates in
    let ys = c.`out_wires in
    let max_wire = topo.`npinputs + topo.`nsinputs + topo.`ngates in
    let ntopo = {| npinputs = topo.`npinputs ; nsinputs = topo.`nsinputs ;
                   noutputs = topo.`noutputs ; ngates = topo.`ngates + 2 |} in
    let ngg = Multiplication (max_wire + 1) (Constant max_wire fone) gg in
    {| topo = ntopo ; gates = ngg ; out_wires = ys|}.
  
  (** Randomness validity predicate for the prover. We consider the prover randomness to be valid
      if it has the correct number of elements and if the last [a] element of the prover 
      randomness is different than 0 *)
  op valid_rand_prover' (r : prover_rand_t) (gg : gates_t) : bool =
    with gg = PInput _ => true
    with gg = SInput _ => true
    with gg = Constant _ _ => true
    with gg = Addition gid wl wr => (*valid_rand_prover' r wl /\ valid_rand_prover' r wr*)
      let gid_l = get_gid wl in
      let gid_r = get_gid wr in
      (nth def_ui r gid).`a = fadd (nth def_ui r gid_l).`a (nth def_ui r gid_r).`a /\
      (nth def_ui r gid).`b = fadd (nth def_ui r gid_l).`b (nth def_ui r gid_r).`b /\
      valid_rand_prover' r wl /\ valid_rand_prover' r wr
    with gg = Multiplication _ wl wr => valid_rand_prover' r wl /\ valid_rand_prover' r wr.

  op valid_rand_prover (r : prover_rand_t) (x : prover_input_t) : bool =
    let (w, st) = x in
    let (c, inst) = st in
    let topo = c.`topo in
    let gg = c.`gates in
    size r = topo.`nsinputs + topo.`npinputs + topo.`ngates + 2 /\ 
    (forall k, 0 <= k < size r => 
      (nth def_ui r k).`a <> fzero). (*/\ valid_rand_prover' r gg.*) (*/\
    (*(nth def_ui r (get_gid gg)).`a <> fzero /\*)
    valid_rand_prover' r gg.
(*    (forall k, 0 <= k < size r => 
      is_addition (oget (get_gate gg k)) =>
        (nth def_ui r k).`a = fadd (nth def_ui r (get_gid (as_addition (oget (get_gate gg k))).`2)).`a 
                                   (nth def_ui r (get_gid (as_addition (oget (get_gate gg k))).`3)).`a) /\
    (forall k, 0 <= k < size r => 
      is_addition (oget (get_gate gg k)) =>
        (nth def_ui r k).`a = fadd (nth def_ui r (get_gid (as_addition (oget (get_gate gg k))).`2)).`a 
                                   (nth def_ui r (get_gid (as_addition (oget (get_gate gg k))).`3)).`a).
*)*)
  (** Verifier randomness specification *)
  (** The verifier will have a list composed of two field elements (v and v') per gate *)
  type yi_t = { v : t ; v' : t }.
  (** Default value for an element of the verifier randomness *)
  op def_yi : yi_t = {| v = fzero ; v' = fzero |}.
  (** The type of lists of elements of type [yi_t] *)
  type y_t = yi_t list.
  (** The verifier randomness is a finite field element and a list of elements of type [yi_t] *)
  type verifier_rand_t = { alpha : t ; y : y_t }.

  (** Auxiliar verifier create the prover verifier randomness. This operator is only needed for
      the array-based optimization *)
  op create_verifier_rand (alpha : t) (y : yi_t list) = {| alpha = alpha ; y = y |}.

  (** Randomness validity predicate for the verifier. We consider the verifier randomness to be 
      valid if it has the correct number of elements and if the verifier and prover randomness
      are correlated with respect to an affine function that evaluates to 𝛼 *)  
  op valid_rand_verifier (rp : prover_rand_t) (rv : verifier_rand_t) (x : verifier_input_t) : bool =
    let alpha = rv.`alpha in 
    let y = rv.`y in
    let (c, inst) = x in
    let gg = c.`gates in
    size y = size rp /\
    (forall k, 0 <= k < size y => 
      (nth def_yi y k).`v = fadd (fmul alpha (nth def_ui rp k).`a) (nth def_ui rp k).`b) /\
    (forall k, 0 <= k < size y => 
      (nth def_yi y k).`v' = fadd (fmul alpha (nth def_ui rp k).`a') (nth def_ui rp k).`b').

  (** Prover output type. At the end of the protocol, the prover has no output *)
  type prover_output_t = unit. 
  (** Verifier output type. At the end of the protocol, the verifier outputs a boolean, stating
      if it accepts the proof or not *)
  type verifier_output_t = bool.

  (** Commitment type for individual gates. For each circuit gate, the prover commits values 
      [m], [m'] and [c], captured by the [zi_t] record type *)
  type zi_t = { m : t ; m' : t ; c : t }.

  (** We model the commitment message as a tree, following the same format used for the 
      definition of arithmetic circuits *)
  type z_t = [
    | PInputZ of wid_t & zi_t
    | SInputZ of wid_t & zi_t
    | ConstantZ of gid_t & zi_t
    | AdditionZ of gid_t & zi_t & z_t & z_t
    | MultiplicationZ of gid_t & zi_t & z_t & z_t
  ].

  op is_pinputz (z : z_t) : bool =
    with z = PInputZ _ _ => true
    with z = SInputZ _ _ => false
    with z = ConstantZ _ _ => false
    with z = AdditionZ _ _ _ _ => false
    with z = MultiplicationZ _ _ _ _ => false.
  op is_sinputz (z : z_t) : bool =
    with z = PInputZ _ _ => false
    with z = SInputZ _ _ => true
    with z = ConstantZ _ _ => false
    with z = AdditionZ _ _ _ _ => false
    with z = MultiplicationZ _ _ _ _ => false.
  op is_constantz (z : z_t) : bool =
    with z = PInputZ _ _ => false
    with z = SInputZ _ _ => false
    with z = ConstantZ _ _ => true
    with z = AdditionZ _ _ _ _ => false
    with z = MultiplicationZ _ _ _ _ => false.
  op is_additionz (z : z_t) : bool =
    with z = PInputZ _ _ => false
    with z = SInputZ _ _ => false
    with z = ConstantZ _ _ => false
    with z = AdditionZ _ _ _ _ => true
    with z = MultiplicationZ _ _ _ _ => false.
  op as_additionz (z : z_t) =
    with z = PInputZ _ _ => witness
    with z = SInputZ _ _ => witness
    with z = ConstantZ _ _ => witness
    with z = AdditionZ gid zi zl zr => (gid, zi, zl, zr)
    with z = MultiplicationZ _ _ _ _ => witness.
  op is_multiplicationz (z : z_t) : bool =
    with z = PInputZ _ _ => false
    with z = SInputZ _ _ => false
    with z = ConstantZ _ _ => false
    with z = AdditionZ _ _ _ _ => false
    with z = MultiplicationZ _ _ _ _ => true.
  op as_multiplicationz (z : z_t) =
    with z = PInputZ _ _ => witness
    with z = SInputZ _ _ => witness
    with z = ConstantZ _ _ => witness
    with z = AdditionZ _ _ _ _ => witness
    with z = MultiplicationZ gid zi zl zr => (gid, zi, zl, zr).
  
  (** Generates the [z] data structure, based on the prover algorithm described before *)
  op gen_z (u : prover_rand_t) (gg : gates_t) (xp : t list) (xs : t list) : z_t =
    with gg = PInput wid => 
      let b = (nth def_ui u wid).`b in
      let w = eval_gates gg xp xs in
      PInputZ wid {| m = fsub w b ; m' = fzero ; c = fzero |}

    with gg = SInput wid => 
      let b = (nth def_ui u wid).`b in
      let w = eval_gates gg xp xs in
      SInputZ wid {| m = fsub w b ; m' = fzero ; c = fzero |}

    with gg = Constant gid c => 
      let b = (nth def_ui u gid).`b in
      let w = eval_gates gg xp xs in
      ConstantZ gid {| m = fsub w b ; m' = fzero ; c = fzero |}

    with gg = Addition gid wl wr =>
      let b = (nth def_ui u gid).`b in
      let w = eval_gates gg xp xs in
      AdditionZ gid {| m = fsub w b ; m' = fzero ; c = fzero |} (gen_z u wl xp xs) (gen_z u wr xp xs)

    with gg = Multiplication gid l r => 
      let wl = eval_gates l xp xs in
      let wr = eval_gates r xp xs in
      let w = fmul wl wr in

      let ui = nth def_ui u gid in
      let a = ui.`a in
      let b = ui.`b in
      let a' = ui.`a' in
      let b' = ui.`b' in

      let ul = nth def_ui u (get_gid l) in
      (*let al = if (is_addition l) then 
                 fadd (nth def_ui u (get_gid (as_addition l).`2)).`a 
                      (nth def_ui u (get_gid (as_addition r).`3)).`a else ul.`a in
      let bl = if (is_addition l) then 
                 fadd (nth def_ui u (get_gid (as_addition l).`2)).`b
                      (nth def_ui u (get_gid (as_addition r).`3)).`b else ul.`a in*)
      let al = ul.`a in
      let bl = ul.`b in

      let al' = ul.`a' in
      let bl' = ul.`b' in

      let ur = nth def_ui u (get_gid r) in
      let ar = ur.`a in
      let br = ur.`b in
      let ar' = ur.`a' in
      let br' = ur.`b' in

      MultiplicationZ gid {| m = fsub w b ;
                             m' = fsub (fmul al ar) a' ;
                             c = fsub (fsub (fadd (fmul al wr) (fmul ar wl)) a) b' |}
                          (gen_z u l xp xs) (gen_z u r xp xs).

  op get_c (z : z_t) : t list =
    with z = PInputZ wid zi => []
    with z = SInputZ wid zi => []
    with z = ConstantZ gid zi => []
    with z = AdditionZ gid zi zl zr => [] ++ get_c zl ++ get_c zr
    with z = MultiplicationZ gid zi zl zr =>  [zi.`c] ++ get_c zl ++ get_c zr.

  (** Gets the random [a] value from the prover randomness, i.e., gets the [a] random value
      associated with the ouput circuit gate *)
  op get_a (u : prover_rand_t) (gg : gates_t) : t =
    let gid = get_gid gg in
    let ui = nth def_ui u gid in
    ui.`a.

  (* The final commitment message is comprised of the [z_t] tree structure and of a finite field 
      value *)
  type commitment_t = z_t * t.

  (** Commitment function.

      Informally, the commitment message is built based on two operators: [gen_z] - transverses 
      the circuit and produces the three commitment values [m], [c] and [c'] for each gate - and 
      [get_a] - outputs the random a value for the output gate of the circuit. 

      Before starting the commitment computation, the prover first invokes a pre-processing 
      function dubbed [add_final_mul]. This function forces all circuits to end in a 
      multiplication gate by adding a final multiplication gate to the root of the circuit tree *)
  op commit (r : prover_rand_t) (x : prover_input_t) : commitment_t = 
    let (w, st) = x in
    let (c, inst) = st in
    let c = add_final_mul c in
    let topo = c.`topo in
    let gg = c.`gates in
    let z = gen_z r gg inst w in
    let a = (get_a r gg) in
    (z, a).

  (** Verifier data type for individual gates. For each circuit gate, the verifier will produce 
      values [e], [e'] and [e''], captured by the [fi_t] record type *)
  type fi_t = { e : t ; e' : t ; e'' : t }.

  (** We model the [f] data type as a tree, following the same format used for the 
      definition of arithmetic circuits *)
  type f_t = [
    | PInputF of fi_t
    | SInputF of fi_t
    | ConstantF of fi_t
    | AdditionF of fi_t & f_t & f_t
    | MultiplicationF of fi_t & f_t & f_t
  ].

  (** Returns the [f] data type of a gate *)
  op get_fi (f : f_t) : fi_t =
    with f = PInputF fi => fi
    with f = SInputF fi => fi
    with f = ConstantF fi => fi
    with f = AdditionF fi fl fr => fi
    with f = MultiplicationF fi fl fr => fi.

  (** Returns the [e] value from the [f] data type of a gate *)
  op get_e (f : f_t) : t = (get_fi f).`e.

  (** Generates the [f] data structure, based on the verifier algorithm described before *)
  op gen_f (r : verifier_rand_t) (z : z_t) =
    with z = PInputZ wid zi => 
      let m = zi.`m in
      let v = (nth def_yi r.`y wid).`v in
      PInputF {| e = fadd v m ; e' = fzero ; e'' = fzero |}

    with z = SInputZ wid zi => 
      let m = zi.`m in
      let v = (nth def_yi r.`y wid).`v in
      SInputF {| e = fadd v m ; e' = fzero ; e'' = fzero |}

    with z = ConstantZ gid zi =>
      let m = zi.`m in
      let v = (nth def_yi r.`y gid).`v in
      ConstantF {| e = fadd v m ; e' = fzero ; e'' = fzero |}

    with z = AdditionZ gid zi zl zr =>
      let fl = gen_f r zl in
      let fr = gen_f r zr in

      let m = zi.`m in
      let v = (nth def_yi r.`y gid).`v in

      AdditionF {| e = fadd v m (*fadd (get_e fl) (get_e fr)*) ; e' = fzero ; e'' = fzero |} fl fr

    with z = MultiplicationZ gid zi zl zr =>
      let fl = gen_f r zl in
      let fr = gen_f r zr in

      let m = zi.`m in
      let m' = zi.`m' in

      let alpha = r.`alpha in
      let y = nth def_yi r.`y gid in
      let v = y.`v in
      let v' = y.`v' in

      let el = get_e fl in
      let er = get_e fr in

      let e = fadd v m in
      let e' = fadd v' (fmul alpha m') in
      let e'' = fsub (fsub (fmul el er) e) (fmul alpha e') in
      
      MultiplicationF {| e = e ; e' = e' ; e'' = e'' |} fl fr.

  (** Checks that the commitment message received was produce for a specific circuit. Essentially,
      it will check that for each gate in the circuit, there a counterpart in the commitment
      message produced by the prover *)
  op valid_z_gates (z : z_t) (gg : gates_t) : bool =
    with z = PInputZ wid _ => if is_pinput gg then as_pinput gg = wid else false
    with z = SInputZ wid _ => if is_sinput gg then as_sinput gg = wid else false
    with z = ConstantZ gid _ => if is_constant gg then (as_constant gg).`1 = gid else false
    with z = AdditionZ gid _ zl zr => 
      if is_addition gg then
        let (gid', wl, wr) = as_addition gg in
        gid = gid' /\ valid_z_gates zl wl /\ valid_z_gates zr wr
      else false
    with z = MultiplicationZ gid _ zl zr =>
      if is_multiplication gg then
        let (gid', wl, wr) = as_multiplication gg in
        gid = gid' /\ valid_z_gates zl wl /\ valid_z_gates zr wr
      else false.

  (** Simplified calling interface of the [valid_z_gates] function *)
  op valid_z (z : z_t) (c : circuit_t): bool =
    valid_z_gates z c.`gates.

  (** Proves that a [z] message is always valid for the set of gates it was produced from *)
  lemma valid_z_gen (u : prover_rand_t) (gg : gates_t) (inst : t list) (wit : t list) :
    valid_z_gates (gen_z u gg inst wit) gg. 
  proof. elim gg => //=. qed.

  (** Prove function.

      To validate a proof, the verifier first checks that the message it received is consistent 
      with the original circuit, meaning that it will check if the prover produced a commitment 
      for the actual circuit being evaluated. If this is the case, then the verifier will compute
      [f] in order to obtain the value [e] and for the output gate using the operator 
      [get_e] and check if e it is equal to n𝛼.
  *)
  op batch_check (f : f_t) (z : z_t) (alpha : t) : bool = 
    with f = PInputF _ => is_pinputz z
    with f = SInputF _ => is_sinputz z
    with f = ConstantF _ => is_constantz z
    with f = AdditionF _ fl fr => 
      if (is_additionz z) then
        batch_check fl (as_additionz z).`3 alpha /\
        batch_check fr (as_additionz z).`4 alpha
      else false
    with f = MultiplicationF fi fl fr => 
      if (is_multiplicationz z) then
        fi.`e'' = fmul alpha (as_multiplicationz z).`2.`c /\
        batch_check fl (as_multiplicationz z).`3 alpha /\
        batch_check fr (as_multiplicationz z).`4 alpha
      else false.

lemma get_fi_exec rp rv circ w inst :
valid_circuit circ =>
valid_rand_prover rp (w, (circ, inst)) =>
valid_rand_verifier rp rv (circ, inst) =>
(get_fi (gen_f rv (gen_z rp circ.`gates inst w))).`e = 
  fadd (fmul rv.`alpha (nth def_ui rp (get_gid circ.`gates)).`a) (eval_gates circ.`gates inst w).
proof.
elim circ => topo gg out //=.
rewrite /valid_circuit //=.
rewrite /valid_rand_prover //=.
rewrite /valid_rand_verifier //=.
rewrite /valid_gates //=.
progress.

move : H0 H1 H2 H5.
elim gg => //=.
move => wid; progress.
rewrite H7.
smt().
ringeq.

move => wid; progress.
rewrite H7.
smt().
ringeq.

move => gid; progress.
rewrite H7.
smt().
ringeq.

move => gid wl wr; progress.
rewrite /get_e //=.
rewrite H7.
smt().
ringeq.

(*rewrite H0 //=.
rewrite H1 //=.
rewrite H21 //=.
ringeq.*)

move => gid wl wr; progress.
rewrite H7 //=.
smt().
ringeq.
qed.

lemma batch_check_true rp rv circ w inst :
valid_circuit circ =>
valid_rand_prover rp (w, (circ, inst)) =>
valid_rand_verifier rp rv (circ, inst) =>
  batch_check (gen_f rv (gen_z rp circ.`gates inst w)) (gen_z rp circ.`gates inst w) rv.`alpha.
proof.
elim circ => topo gg out //=.
rewrite /valid_circuit //= /valid_rand_prover //= /valid_rand_verifier //=.
progress.
move : H0.
elim gg => //=.
move => gid l r; progress.
rewrite !H0.
smt().
smt().
(*smt().*)

move => gid l r; progress.
rewrite /get_e //=.
have ->: (get_fi (gen_f rv (gen_z rp l inst w))).`e = 
          fadd (fmul rv.`alpha (nth def_ui rp (get_gid l)).`a) (eval_gates l inst w).
rewrite (get_fi_exec rp rv {| topo = topo ; gates = l ; out_wires = out |} w inst).
smt().
rewrite /valid_rand_prover //=.
smt().
smt().
have ->: (get_fi (gen_f rv (gen_z rp r inst w))).`e = 
          fadd (fmul rv.`alpha (nth def_ui rp (get_gid r)).`a) (eval_gates r inst w).
rewrite (get_fi_exec rp rv {| topo = topo ; gates = r ; out_wires = out |} w inst).
smt().
smt().
smt().
done.
rewrite H5.
smt().
rewrite H6 //=.
smt().
ringeq.
smt().
smt().
qed.

  op prove (r : verifier_rand_t) (x : verifier_input_t) (c : commitment_t) : bool =
    let (z, z') = c in
    let (circ, inst) = x in
    if (valid_circuit circ) then
      let circ = add_final_mul circ in
      let n = z' in
      if valid_z z circ /\ n <> fzero then
        let f = gen_f r z in
        if (batch_check f z r.`alpha) then
          get_e f = fmul n r.`alpha
        else false
      else false
    else false.

  (** Message of the protocol. For the case of DVNIZK protocols, it consists solely of the 
      commitment message *)
  type trace_t = commitment_t.

 (** Protocol operation. This operation specifies an honest execution of the protocol, by
      sequentially executing the prover and the verifier, returning both outputs and message
      trace *)
  op protocol (r : prover_rand_t * verifier_rand_t) 
              (x : prover_input_t * verifier_input_t) : 
              trace_t * (prover_output_t * verifier_output_t) = 
    let (r_p, r_v) = r in let (x_p, x_v) = x in
    let c = commit r_p x_p in
    let b = prove r_v x_v c in (c, ((),b)).

  (** Instantiation of the DVNIZK protocol syntax with the concrete LPZK types and operators.
      Informally, one can see this operation as the definition of LPZK as a DVNIZK object 
      (similar to what happens with Java classes) *)
  clone import DVNIZKProtocol with
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
realize correct.
  (** Correctness lemma. Proves that the protocol securely evaluates the relation, i.e.:
        - if the witness and statement are not in the relation, then the protocol always outputs
          false; and
        - if the witness and statement are in the relation, then the protocol always outputs true
  *)
    rewrite /valid_inputs /valid_rands /valid_circuit /valid_topology /valid_rand_prover 
            /valid_rand_verifier /protocol /commit /prove /relation /add_final_mul /valid_gates.
    move => [rp] rv [xp] xv => />.
    elim xp => w stp => />.
    elim xv => c inst => />.
    elim c => topo gg ys => />.
    progress.
rewrite /valid_z //= /get_e //= /get_a //=.
rewrite valid_z_gen //=. 
have ->: batch_check (gen_f rv (gen_z rp gg inst w)) (gen_z rp gg inst w) rv.`alpha.
print batch_check_true.
rewrite (batch_check_true rp rv {| topo = topo ; gates = gg ; out_wires = ys |} w inst).
smt().
smt().
smt().

simplify.
have ->: valid_circuit {| topo = topo; gates = gg; out_wires = ys; |} by smt().

have ->: fsub
   (fsub
      (fmul
         (fadd
            (nth def_yi rv.`y
               (topo.`npinputs + topo.`nsinputs + topo.`ngates)).`v
            (fsub fone
               (nth def_ui rp
                  (topo.`npinputs + topo.`nsinputs + topo.`ngates)).`b))
         (get_fi (gen_f rv (gen_z rp gg inst w))).`e)
      (fadd
         (nth def_yi rv.`y
            (topo.`npinputs + topo.`nsinputs + topo.`ngates + 1)).`v
         (fsub (fmul fone (eval_gates gg inst w))
            (nth def_ui rp
               (topo.`npinputs + topo.`nsinputs + topo.`ngates + 1)).`b)))
   (fmul rv.`alpha
      (fadd
         (nth def_yi rv.`y
            (topo.`npinputs + topo.`nsinputs + topo.`ngates + 1)).`v'
         (fmul rv.`alpha
            (fsub
               (fmul
                  (nth def_ui rp
                     (topo.`npinputs + topo.`nsinputs + topo.`ngates)).`a
                  (nth def_ui rp (get_gid gg)).`a)
               (nth def_ui rp
                  (topo.`npinputs + topo.`nsinputs + topo.`ngates + 1)).`a')))) =
 fmul rv.`alpha
   (fsub
      (fsub
         (fadd
            (fmul
               (nth def_ui rp
                  (topo.`npinputs + topo.`nsinputs + topo.`ngates)).`a
               (eval_gates gg inst w))
            (fmul (nth def_ui rp (get_gid gg)).`a fone))
         (nth def_ui rp (topo.`npinputs + topo.`nsinputs + topo.`ngates + 1)).`a)
      (nth def_ui rp (topo.`npinputs + topo.`nsinputs + topo.`ngates + 1)).`b').
rewrite !H15 //=.
smt().
rewrite !H14 //=.
smt().
smt().
(*smt.
rewrite H15 //= 1:/#.
print get_fi_exec.*)
rewrite (get_fi_exec rp rv {| topo = topo ; gates = gg ; out_wires = ys |} w inst).
smt().
smt().
smt().

simplify.
move : H6 H5 H4.
elim gg => //=.

move => wid; progress.
ringeq.

move => wid; progress.
ringeq.

move => gid c; progress.
ringeq.

move => gid l r; progress.
ringeq.

move => gid l r; progress.
ringeq.
simplify.

have ->: (nth def_ui rp (topo.`npinputs + topo.`nsinputs + topo.`ngates + 1)).`a <> fzero.
smt().
simplify.

move : H4 H6 H5; elim gg => //=.
    (* Public input gate *)
    move => wid => />; progress.
    rewrite /eval_circuit /get_e /get_a /=.
    pose max_wire := topo.`npinputs + topo.`nsinputs + topo.`ngates + 1.
    rewrite H14 1:/#.
    case (nth fzero inst wid = fzero); progress.
      rewrite H6 mulf0.
      by have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth def_ui rp max_wire).`b) (fsub fzero (nth def_ui rp max_wire).`b) = fmul (nth def_ui rp max_wire).`a rv.`alpha by ringeq.
      rewrite mul1f.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth def_ui rp max_wire).`b) (fsub (nth fzero inst wid) (nth def_ui rp max_wire).`b) = fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth fzero inst wid) by ringeq.
      have ->: fmul rv.`alpha (nth def_ui rp max_wire).`a = fmul (nth def_ui rp max_wire).`a rv.`alpha by ringeq.
    by rewrite non_zero_add.
    (* Secret input gate *)
    move => wid => />; progress.
    rewrite /eval_circuit /get_e /get_a /=.
    pose max_wire := topo.`npinputs + topo.`nsinputs + topo.`ngates + 1.
    rewrite H14 1:/#.
    case (nth fzero w wid = fzero); progress.
      rewrite H6 mulf0.
      by have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth def_ui rp max_wire).`b) (fsub fzero (nth def_ui rp max_wire).`b) = fmul (nth def_ui rp max_wire).`a rv.`alpha by ringeq.
      rewrite mul1f.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth def_ui rp max_wire).`b) (fsub (nth fzero w wid) (nth def_ui rp max_wire).`b) = fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth fzero w wid) by ringeq.
      have ->: fmul rv.`alpha (nth def_ui rp max_wire).`a = fmul (nth def_ui rp max_wire).`a rv.`alpha by ringeq.
    by rewrite non_zero_add.
    (* Constant gate *)
    move => gid c => />; progress.
    rewrite /eval_circuit /get_e /get_a /=.
    pose max_wire := topo.`npinputs + topo.`nsinputs + topo.`ngates + 1.
    rewrite H14 1:/#.
    case (c = fzero); progress.
      rewrite mulf0.
      by have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth def_ui rp max_wire).`b) (fsub fzero (nth def_ui rp max_wire).`b) = fmul (nth def_ui rp max_wire).`a rv.`alpha by ringeq.
      rewrite mul1f.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth def_ui rp max_wire).`b) (fsub c (nth def_ui rp max_wire).`b) = fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) c by ringeq.
      have ->: fmul rv.`alpha (nth def_ui rp max_wire).`a = fmul (nth def_ui rp max_wire).`a rv.`alpha by ringeq.
    by rewrite non_zero_add.
    (* Addition gate *)
    move => gid l r; rewrite /eval_circuit /get_e /get_a /=; progress.  
    rewrite /eval_circuit /get_e /get_a /=; progress. 
    move : H4; rewrite H6 H25 H27; progress.
    move : H5; rewrite H16 H26 H28; progress.
    rewrite /get_e /=.
    pose max_wire := topo.`npinputs + topo.`nsinputs + topo.`ngates + 1.
    rewrite H14 //= 1:/#.
    case (fadd (eval_gates l inst w) (eval_gates r inst w) = fzero); progress.
      rewrite H29 mulf0.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth def_ui rp max_wire).`b) (fsub fzero (nth def_ui rp max_wire).`b) = fmul (nth def_ui rp max_wire).`a rv.`alpha by ringeq.
      by smt(@PrimeField).
      rewrite mul1f.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth def_ui rp max_wire).`b) (fsub (fadd (eval_gates l inst w) (eval_gates r inst w)) (nth def_ui rp max_wire).`b) = fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (fadd (eval_gates l inst w) (eval_gates r inst w)) by ringeq.
      have ->: fmul rv.`alpha (nth def_ui rp max_wire).`a = fmul (nth def_ui rp max_wire).`a rv.`alpha by ringeq.
    by rewrite non_zero_add.
    (* Multiplication gate *)
    move => gid l r; rewrite /eval_circuit /get_e /get_a /=; progress.  
    rewrite /eval_circuit /get_e /get_a /=; progress. 
    move : H4; rewrite H6 H25 H27; progress.
    move : H5; rewrite H16 H26 H28; progress.
    rewrite /get_e /=.
    pose max_wire := topo.`npinputs + topo.`nsinputs + topo.`ngates + 1.
    rewrite H14 //= 1:/#.
    case (fmul (eval_gates l inst w) (eval_gates r inst w) = fzero); progress.
      rewrite H29 mulf0.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth def_ui rp max_wire).`b) (fsub fzero (nth def_ui rp max_wire).`b) = fmul (nth def_ui rp max_wire).`a rv.`alpha by ringeq.
      by smt(@PrimeField).
      rewrite mul1f.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (nth def_ui rp max_wire).`b) (fsub (fmul (eval_gates l inst w) (eval_gates r inst w)) (nth def_ui rp max_wire).`b) = fadd (fmul rv.`alpha (nth def_ui rp max_wire).`a) (fmul (eval_gates l inst w) (eval_gates r inst w)) by ringeq.
      have ->: fmul rv.`alpha (nth def_ui rp max_wire).`a = fmul (nth def_ui rp max_wire).`a rv.`alpha by ringeq.
    by rewrite non_zero_add.
qed.

  (** Completeness proof *)
  (** First, we import the completeness security definition instantiated with LPZK *)
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
        the correctness proof above. *)
    lemma completeness &m w_ x_ : 
                                  Pr[Completeness(R).main(w_,x_) @ &m : res] = 1%r.
    proof.
      byphoare (_ : w_ = w /\ x = x_ ==> res) => //.
      proc.
      seq 1 : #pre => //.
        by call r_gen_ll.
        by wp; skip; progress; move : (correct (r_p{hr}, r_v{hr}) ((w{hr}, x{hr}), x{hr})) => /#.
        by hoare; call (_ : true).
      qed.

  end section Completeness.

  (** Soundness proof *)
  (** First, we import the soundness security definition instantiated with LPZK *)
  clone import Soundness as LPZKSoundness with
    theory DVNIZKProtocol <- DVNIZKProtocol.

  section Soundness.

    (** We write a concrete randomness generator for the verifier. It receives as input the
        prover randomness, samples a value 𝛼 at random and then computes the correct
        correlated randomness in accordance with the dealer algorithm *)
    module RV : RandV_t = {
      proc gen(rp : prover_rand_t) : verifier_rand_t = {
        var alpha, y;

        alpha <$ FDistr.dt;
        y <- map (fun u => {| v = fadd (fmul alpha u.`a) u.`b ; v' = fadd (fmul alpha u.`a') u.`b' |}) rp;

        return ({| alpha = alpha; y = y |});
      }
    }.
  
    (** Malicious prover declaration *)
    declare module MP <: MProver_t.

    (** Assumes that the malicious prover produces commitments in the appropriate [z] format *)
    axiom mp_commit_exec (rp_ : prover_rand_t) (x_ : statement_t) :
      hoare [ MP.commit : rp_ = rp /\ x_ = x ==> 
                exists w, res.`1 = gen_z rp_ (add_final_mul x_.`1).`gates x_.`2 w].

    (** Soundness lemma, according to the soundness game of the *CompletenessDVNIZKP.ec* file.
        We prove that a malicious prover can trick an honest verifier into accepting a false
        proof with probability less than [1/q], with [q] being the order of the finite field *)
    lemma soundness &m (x_ : statement_t) rp_ :
      valid_rand_prover rp_ (witness, x_) =>
                                 Pr [ Soundness(RV, MP).main(rp_, x_) @ &m : res ] <= 1%r / q%r.
    proof.
      progress; byphoare (_ : rp = rp_ /\ x = x_ ==> res) => //=.
      proc; inline*.
      rcondt 6.
        wp; rnd; wp; call (_ : true); wp; skip; progress.
          rewrite /valid_rand_verifier //=.
          elim (x{hr}) => circ inst //=; progress.
          by simplify; rewrite size_map //=.
          by rewrite (nth_map def_ui def_yi); first by move : H2; rewrite size_map.
          by rewrite (nth_map def_ui def_yi); first by move : H2; rewrite size_map.
      wp; rnd; wp; simplify; call (mp_commit_exec rp_ x_); skip; progress.
      case (! language x{hr}); progress; last by rewrite mu0; smt.
      rewrite /prove /=.
      (*move : H H0 H1 H2 H3.
      rewrite /valid_circuit //= /valid_gates //=.*)
      move : H H0 H1.
      elim result => z n /=.
      elim (x{hr}) => c inst. 
      elim c => topo gg ys /=.
      progress.
      rewrite /add_final_mul /= /valid_z /= /get_e /get_fi /=.
      pose max_wire := topo.`npinputs + topo.`nsinputs + topo.`ngates.
      case (valid_z_gates (gen_z rp{hr} gg inst w) gg); progress; last by rewrite mu0; smt.
simplify.
case (n <> fzero); progress; last by rewrite mu0; smt.
simplify.
case (valid_circuit {| topo = topo; gates = gg; out_wires = ys; |}); progress; last by rewrite mu0; smt.

have ->: (fun (x0 : t) =>
     (fsub
        (fsub
           (fmul
              (fadd
                 (nth def_yi
                    (map
                       (fun (u : ui_t) =>
                          {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                              fadd (fmul x0 u.`a') u.`b'; |}) rp{hr})
                    max_wire).`v
                 (fsub fone (nth def_ui rp{hr} max_wire).`LPZK.b))
              (get_fi
                 (gen_f
                    {| alpha = x0; y =
                        map
                          (fun (u : ui_t) =>
                             {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                                 fadd (fmul x0 u.`a') u.`b'; |}) rp{hr}; |}
                    (gen_z rp{hr} gg inst w))).`e)
           (fadd
              (nth def_yi
                 (map
                    (fun (u : ui_t) =>
                       {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                           fadd (fmul x0 u.`a') u.`b'; |}) rp{hr})
                 (max_wire + 1)).`v
              (fsub (fmul fone (eval_gates gg inst w))
                 (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b)))
        (fmul x0
           (fadd
              (nth def_yi
                 (map
                    (fun (u : ui_t) =>
                       {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                           fadd (fmul x0 u.`a') u.`b'; |}) rp{hr})
                 (max_wire + 1)).`v'
              (fmul x0
                 (fsub
                    (fmul (nth def_ui rp{hr} max_wire).`a
                       (nth def_ui rp{hr} (get_gid gg)).`a)
                    (nth def_ui rp{hr} (max_wire + 1)).`a')))) =
      fmul x0
        (fsub
           (fsub
              (fadd
                 (fmul (nth def_ui rp{hr} max_wire).`a (eval_gates gg inst w))
                 (fmul (nth def_ui rp{hr} (get_gid gg)).`a fone))
              (nth def_ui rp{hr} (max_wire + 1)).`a)
           (nth def_ui rp{hr} (max_wire + 1)).`b') /\
      batch_check
        (gen_f
           {| alpha = x0; y =
               map
                 (fun (u : ui_t) =>
                    {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                        fadd (fmul x0 u.`a') u.`b'; |}) rp{hr}; |}
           (gen_z rp{hr} gg inst w)) (gen_z rp{hr} gg inst w) x0) &&
     fadd
       (nth def_yi
          (map
             (fun (u : ui_t) =>
                {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                    fadd (fmul x0 u.`a') u.`b'; |}) rp{hr}) (max_wire + 1)).`v
       (fsub (fmul fone (eval_gates gg inst w))
          (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b) =
     fmul n x0) = 
(fun (x0 : t) =>
     (fsub
        (fsub
           (fmul
              (fadd
                 ((fun (u : ui_t) =>
                          {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                              fadd (fmul x0 u.`a') u.`b'; |}) (nth def_ui rp{hr} max_wire)).`v
                 (fsub fone (nth def_ui rp{hr} max_wire).`LPZK.b))
              (fadd (fmul x0 (nth def_ui rp{hr} (get_gid gg)).`a)
      (eval_gates gg inst w)))
           (fadd
              ((fun (u : ui_t) =>
                       {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                           fadd (fmul x0 u.`a') u.`b'; |}) (nth def_ui rp{hr} (max_wire + 1))).`v
              (fsub (fmul fone (eval_gates gg inst w))
                 (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b)))
        (fmul x0
           (fadd
              ((fun (u : ui_t) =>
                       {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                           fadd (fmul x0 u.`a') u.`b'; |}) (nth def_ui rp{hr} (max_wire + 1))).`v'
              (fmul x0
                 (fsub
                    (fmul (nth def_ui rp{hr} max_wire).`a
                       (nth def_ui rp{hr} (get_gid gg)).`a)
                    (nth def_ui rp{hr} (max_wire + 1)).`a')))) =
      fmul x0
        (fsub
           (fsub
              (fadd
                 (fmul (nth def_ui rp{hr} max_wire).`a (eval_gates gg inst w))
                 (fmul (nth def_ui rp{hr} (get_gid gg)).`a fone))
              (nth def_ui rp{hr} (max_wire + 1)).`a)
           (nth def_ui rp{hr} (max_wire + 1)).`b') /\
      true) &&
     fadd
       ((fun (u : ui_t) =>
                {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                    fadd (fmul x0 u.`a') u.`b'; |}) (nth def_ui rp{hr} (max_wire + 1))).`v
       (fsub (fmul fone (eval_gates gg inst w))
          (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b) =
     fmul n x0).

rewrite fun_ext /(==); progress.
rewrite !(nth_map def_ui def_yi).
smt.
smt().
simplify.
rewrite (get_fi_exec rp{hr} {| alpha = x0; y =
                    map
                      (fun (u : ui_t) =>
                         {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                             fadd (fmul x0 u.`a') u.`b'; |}) rp{hr}; |} {| topo = topo ; gates = gg ; out_wires = ys |} w inst).
smt().
smt().
rewrite /valid_rand_verifier //=.
split.
rewrite size_map //=.
rewrite size_map //=.
progress.
rewrite (nth_map def_ui def_yi) //=.
rewrite (nth_map def_ui def_yi) //=.
simplify.
have ->: batch_check
    (gen_f
       {| alpha = x0; y =
           map
             (fun (u : ui_t) =>
                {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                    fadd (fmul x0 u.`a') u.`b'; |}) rp{hr}; |}
       (gen_z rp{hr} gg inst w)) (gen_z rp{hr} gg inst w) x0.
rewrite (batch_check_true rp{hr} {| alpha = x0; y =
         map
           (fun (u : ui_t) =>
              {| v = fadd (fmul x0 u.`a) u.`LPZK.b; v' =
                  fadd (fmul x0 u.`a') u.`b'; |}) rp{hr}; |} {| topo = topo ; gates = gg ; out_wires = ys |} w inst).
smt().
smt().
rewrite /valid_rand_verifier //=.
split.
rewrite size_map //=.
rewrite size_map //=.
progress.
rewrite (nth_map def_ui def_yi) //=.
rewrite (nth_map def_ui def_yi) //=.
done.
simplify.
have ->: (fun (x0 : t) =>
     fsub
       (fsub
          (fmul
             (fadd
                (fadd (fmul x0 (nth def_ui rp{hr} max_wire).`a)
                   (nth def_ui rp{hr} max_wire).`LPZK.b)
                (fsub fone (nth def_ui rp{hr} max_wire).`LPZK.b))
             (fadd (fmul x0 (nth def_ui rp{hr} (get_gid gg)).`a)
                (eval_gates gg inst w)))
          (fadd
             (fadd (fmul x0 (nth def_ui rp{hr} (max_wire + 1)).`a)
                (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b)
             (fsub (fmul fone (eval_gates gg inst w))
                (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b)))
       (fmul x0
          (fadd
             (fadd (fmul x0 (nth def_ui rp{hr} (max_wire + 1)).`a')
                (nth def_ui rp{hr} (max_wire + 1)).`b')
             (fmul x0
                (fsub
                   (fmul (nth def_ui rp{hr} max_wire).`a
                      (nth def_ui rp{hr} (get_gid gg)).`a)
                   (nth def_ui rp{hr} (max_wire + 1)).`a')))) =
     fmul x0
       (fsub
          (fsub
             (fadd
                (fmul (nth def_ui rp{hr} max_wire).`a (eval_gates gg inst w))
                (fmul (nth def_ui rp{hr} (get_gid gg)).`a fone))
             (nth def_ui rp{hr} (max_wire + 1)).`a)
          (nth def_ui rp{hr} (max_wire + 1)).`b') &&
     fadd
       (fadd (fmul x0 (nth def_ui rp{hr} (max_wire + 1)).`a)
          (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b)
       (fsub (fmul fone (eval_gates gg inst w))
          (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b) =
     fmul n x0) = 
(fun (x0 : t) =>
     fsub
       (fsub
          (fmul
             (fadd
                (fadd (fmul x0 (nth def_ui rp{hr} max_wire).`a)
                   (nth def_ui rp{hr} max_wire).`LPZK.b)
                (fsub fone (nth def_ui rp{hr} max_wire).`LPZK.b))
             (fadd (fmul x0 (nth def_ui rp{hr} (get_gid gg)).`a)
                (eval_gates gg inst w)))
          (fadd
             (fadd (fmul x0 (nth def_ui rp{hr} (max_wire + 1)).`a)
                (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b)
             (fsub (fmul fone (eval_gates gg inst w))
                (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b)))
       (fmul x0
          (fadd
             (fadd (fmul x0 (nth def_ui rp{hr} (max_wire + 1)).`a')
                (nth def_ui rp{hr} (max_wire + 1)).`b')
             (fmul x0
                (fsub
                   (fmul (nth def_ui rp{hr} max_wire).`a
                      (nth def_ui rp{hr} (get_gid gg)).`a)
                   (nth def_ui rp{hr} (max_wire + 1)).`a')))) =
     fmul x0
       (fsub
          (fsub
             (fadd
                (fmul (nth def_ui rp{hr} max_wire).`a (eval_gates gg inst w))
                (fmul (nth def_ui rp{hr} (get_gid gg)).`a fone))
             (nth def_ui rp{hr} (max_wire + 1)).`a)
          (nth def_ui rp{hr} (max_wire + 1)).`b') /\
     fadd
       (fadd (fmul x0 (nth def_ui rp{hr} (max_wire + 1)).`a)
          (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b)
       (fsub (fmul fone (eval_gates gg inst w))
          (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b) =
     fmul n x0).
rewrite fun_ext /(==); progress.
smt().

pose q:= (nth def_ui rp{hr} max_wire).`a.
pose e := (nth def_ui rp{hr} max_wire).`LPZK.b.
pose r := (nth def_ui rp{hr} (get_gid gg)).`a.
pose t := (eval_gates gg inst w).
pose y := (nth def_ui rp{hr} (max_wire + 1)).`LPZK.a.
pose u := (nth def_ui rp{hr} (max_wire + 1)).`LPZK.b.
pose i := (nth def_ui rp{hr} (max_wire + 1)).`a'.
pose o := (nth def_ui rp{hr} (max_wire + 1)).`b'.

have ->: (fun (x0 : t) =>
     fsub
       (fsub
          (fmul (fadd (fadd (fmul x0 q) e) (fsub fone e))
             (fadd (fmul x0 r) t))
          (fadd (fadd (fmul x0 y) u) (fsub (fmul fone t) u)))
       (fmul x0 (fadd (fadd (fmul x0 i) o) (fmul x0 (fsub (fmul q r) i)))) =
     fmul x0 (fsub (fsub (fadd (fmul q t) (fmul r fone)) y) o) /\
     fadd (fadd (fmul x0 y) u) (fsub (fmul fone t) u) = fmul n x0) = 
(fun (x0 : t) => 
     fadd (fadd (fmul x0 y) u) (fsub (fmul fone t) u) = fmul n x0).
rewrite fun_ext /(==); progress.


have ->: (
     fsub
       (fsub
          (fmul (fadd (fadd (fmul x0 q) e) (fsub fone e))
             (fadd (fmul x0 r) t))
          (fadd (fadd (fmul x0 y) u) (fsub (fmul fone t) u)))
       (fmul x0 (fadd (fadd (fmul x0 i) o) (fmul x0 (fsub (fmul q r) i)))) =
     fmul x0 (fsub (fsub (fadd (fmul q t) (fmul r fone)) y) o)) =
(
     fsub
       (fsub (fadd (fadd (fmul (fmul (fexp x0 2) q) r) (fmul (fmul x0 q) t)) (fmul x0 r)) (fmul x0 y))
       (fmul x0 (fadd (fadd (fmul x0 i) o) (fmul x0 (fsub (fmul q r) i)))) =
     fmul x0 (fsub (fsub (fadd (fmul q t) (fmul r fone)) y) o)).

congr.
ringeq.
have ->: (
     fsub
       (fsub
          (fadd (fadd (fmul (fmul (fexp x0 2) q) r) (fmul (fmul x0 q) t))
             (fmul x0 r)) (fmul x0 y))
       (fmul x0 (fadd (fadd (fmul x0 i) o) (fmul x0 (fsub (fmul q r) i)))) =
     fmul x0 (fsub (fsub (fadd (fmul q t) (fmul r fone)) y) o)) =
(
     fsub
       (fsub
          (fadd (fadd (fmul (fmul (fexp x0 2) q) r) (fmul (fmul x0 q) t))
             (fmul x0 r)) (fmul x0 y))
       (fadd (fmul x0 o) ((fmul (fmul (fexp x0 2) q)) r)) =
     fmul x0 (fsub (fsub (fadd (fmul q t) (fmul r fone)) y) o)).
congr.
ringeq.

have ->: (
     fsub
       (fsub
          (fadd (fadd (fmul (fmul (fexp x0 2) q) r) (fmul (fmul x0 q) t))
             (fmul x0 r)) (fmul x0 y))
       (fadd (fmul x0 o) (fmul (fmul (fexp x0 2) q) r)) =
     fmul x0 (fsub (fsub (fadd (fmul q t) (fmul r fone)) y) o)) = 
(
     fsub (fsub (fadd (fmul (fmul x0 q) t) (fmul x0 r)) (fmul x0 y)) (fmul x0 o) =
     fmul x0 (fsub (fsub (fadd (fmul q t) (fmul r fone)) y) o)).
congr.
ringeq.

have ->: (
     fsub (fsub (fadd (fmul (fmul x0 q) t) (fmul x0 r)) (fmul x0 y))
       (fmul x0 o) =
     fmul x0 (fsub (fsub (fadd (fmul q t) (fmul r fone)) y) o)) = 
(
     fsub (fsub (fadd (fmul (fmul x0 q) t) (fmul x0 r)) (fmul x0 y))
       (fmul x0 o) =
     fsub (fsub (fadd (fmul (fmul x0 q) t) (fmul x0 r)) (fmul x0 y))
       (fmul x0 o)).
simplify.
have : forall (a b : t), (a = b) = true <=> a = b by smt().
progress.
rewrite H4.
ringeq.
simplify.
done.

have ->: (fun (x0 : t) =>
     fadd (fadd (fmul x0 y) u) (fsub (fmul fone t) u) = fmul n x0) =
(fun (x0 : t) =>
     fadd (fmul x0 y) t = fmul n x0).
rewrite fun_ext /(==); progress.
congr.
ringeq.

case (y = fzero); progress.
rewrite H4 //=.
have ->: (fun (x0 : t) => fadd (fmul x0 fzero) t = fmul n x0) = 
          (fun (x0 : t) => t = fmul n x0).
rewrite fun_ext /(==); progress.
rewrite mulf0.
rewrite add0f.
done.
have ->: (fun (x0 : t) => t = fmul n x0) = 
         (fun (x0 : t) => x0 = fdiv t n).
rewrite fun_ext /(==); progress.
smt.
rewrite FDistr.dt1E.
smt.

case (t = fzero); progress.
move : H0.
rewrite /language //=.
rewrite /relation //=.
rewrite /eval_circuit //=.
progress.
have : (exists (w0 : witness_t), eval_gates gg inst w0 = fzero).
exists w.
done.
smt().

case (y = n); progress.
rewrite mu0_false.
progress.
smt.
smt.

have ->: (fun (x0 : t) => fadd (fmul x0 y) t = fmul n x0) = (fun (x0 : t) => x0 = (fdiv t (fsub n y))).
rewrite fun_ext /(==); progress.
have ->: fmul x0 y = fmul y x0 by ringeq.
progress.
rewrite test //=.
rewrite test2 //=.
rewrite test3 //=.
smt().
smt().
rewrite FDistr.dt1E.
smt.
qed.

  end section Soundness.

  (** Zero-knowledge proof *)
  (** First, we import the zero-knowledge security definition instantiated with LPZK *)
  clone import ZeroKnowledge as LPZKZeroKnowledge with
    theory DVNIZKProtocol <- DVNIZKProtocol.

  section ZeroKnowledge.

    (** Simulator algorithm that computes the commitment message. The simulator that will execute
        following the exact same steps as the prover but that, because it has no access to the 
        witness, assumes that all witness values are zero *)
    op gen_z_sim (u : prover_rand_t) (gg : gates_t) (xp : t list) : z_t =
      with gg = PInput wid => 
        let b = (nth def_ui u wid).`b in
        let w = fzero in
        PInputZ wid {| m = fsub w b ; m' = fzero ; c = fzero |}

      with gg = SInput wid => 
        let b = (nth def_ui u wid).`b in
        let w = fzero in
        SInputZ wid {| m = fsub w b ; m' = fzero ; c = fzero |}

      with gg = Constant gid c => 
        let b = (nth def_ui u gid).`b in
        let w = fzero in
        ConstantZ gid {| m = fsub w b ; m' = fzero ; c = fzero |}

      with gg = Addition gid wl wr =>
        let b = (nth def_ui u gid).`b in
        let w = fzero in
        AdditionZ gid {| m = fsub w b ; m' = fzero ; c = fzero |} (gen_z_sim u wl xp) (gen_z_sim u wr xp)

      with gg = Multiplication gid l r => 
        let wl = fzero in
        let wr = fzero in
        let w = fmul wl wr in

        let ui = nth def_ui u gid in
        let a = ui.`a in
        let b = ui.`b in
        let a' = ui.`a' in
        let b' = ui.`b' in

        let ul = nth def_ui u (get_gid l) in
        let al = ul.`a in
        let bl = ul.`b in
        let al' = ul.`a' in
        let bl' = ul.`b' in

        let ur = nth def_ui u (get_gid r) in
        let ar = ur.`a in
        let br = ur.`b in
        let ar' = ur.`a' in
        let br' = ur.`b' in

      MultiplicationZ gid {| m = fsub w b ;
                             m' = fsub (fmul al ar) a' ;
                             c = fsub (fsub (fadd (fmul al wr) (fmul ar wl)) a) b' |}
                          (gen_z_sim u l xp) (gen_z_sim u r xp).
  
    (** Auxiliar lemma to be used in the induction proof. It proves that only the first
        [topo.`npinputs + topo.`nsinputs + topo.`ngates] random elements are required to produce 
        a commitment message *)
    lemma gen_z_cat rp topo gg ys inst w x y :
      valid_circuit {| topo = topo ; gates = gg ; out_wires = ys |} =>
      size rp = topo.`nsinputs + topo.`npinputs + topo.`ngates =>
      gen_z (rp ++ [x] ++ [y]) gg inst w = gen_z rp gg inst w.
    proof.
      rewrite /valid_circuit /valid_topology /valid_gates /=; progress.
      move : H4 H5 H6 H7; elim gg => //.
      (* Public input gate *)
      move => wid; progress.
      rewrite !nth_cat /= size_cat /=.
      (have ->: wid < size rp + 1 by smt()) => //=.
      by (have ->: wid < size rp by smt()) => //=. 
      (* Secret input gate *)
      move => wid; progress.
      rewrite !nth_cat /= size_cat /=.
      (have ->: wid < size rp + 1 by smt()) => //=.
      by (have ->: wid < size rp by smt()) => //=. 
      (* Constant gate *)
      move => gid c; progress.
      rewrite !nth_cat /= size_cat /=.
      (have ->: gid < size rp + 1 by smt()) => //=.
      by (have ->: gid < size rp by smt ()) => //=.
      (* Addition gate *)
      move => gid wl wr; progress.
      rewrite !nth_cat /= size_cat /=.
      (have ->: gid < size rp + 1 by smt()) => //=.
      by (have ->: gid < size rp by smt ()) => //=.
      by rewrite H4 //=.
      by rewrite H5 //=. 
      (* Multiplication gate *)
      move => gid wl wr; progress.
      congr.
        rewrite !nth_cat /= size_cat /=.
        (have ->: gid < size rp + 1 by smt()) => //=.
        by (have ->: gid < size rp by smt ()) => //=.
        rewrite !nth_cat /= size_cat /=.
        (have ->: gid < size rp + 1 by smt()) => //=.
        (have ->: gid < size rp by smt ()) => //=.
have ->: get_gid wl < size rp + 1 by smt().
simplify.
have ->:  get_gid wl < size rp by smt().
simplify.
have ->: get_gid wr < size rp + 1 by smt().
simplify.
have ->: get_gid wr < size rp by smt().
done.

        rewrite !nth_cat /= size_cat /=.
        (have ->: gid < size rp + 1 by smt()) => //=.
        (have ->: gid < size rp by smt ()) => //=.
have ->: get_gid wl < size rp + 1 by smt().
simplify.
have ->:  get_gid wl < size rp by smt().
simplify.
have ->: get_gid wr < size rp + 1 by smt().
simplify.
have ->: get_gid wr < size rp by smt().
done.
      by rewrite H4 //=.
      by rewrite H5 //=.
    qed.

    (** Auxiliar lemma to be used in the induction proof. It proves that only the first
        [topo.`npinputs + topo.`nsinputs + topo.`ngates] random elements are required to produce 
        a commitment message *)
    lemma gen_z_sim_cat rp topo gg ys inst x y :
      valid_circuit {| topo = topo ; gates = gg ; out_wires = ys |} =>
      size rp = topo.`nsinputs + topo.`npinputs + topo.`ngates =>
      gen_z_sim (rp ++ [x] ++ [y]) gg inst = gen_z_sim rp gg inst.
    proof.
      rewrite /valid_circuit /valid_topology /valid_gates /=; progress.
      move : H4 H5 H6 H7; elim gg => //.
      (* Public input gate *)
      move => w; progress.
      rewrite !nth_cat /= size_cat /=.
      (have ->: w < size rp + 1 by smt()) => //=.
      by (have ->: w < size rp by smt()) => //=. 
      (* Secret input gate *)
      move => w; progress.
      rewrite !nth_cat /= size_cat /=.
      (have ->: w < size rp + 1 by smt()) => //=.
      by (have ->: w < size rp by smt()) => //=. 
      (* Constant gate *)
      move => gid c; progress.
      rewrite !nth_cat /= size_cat /=.
      (have ->: gid < size rp + 1 by smt()) => //=.
      by (have ->: gid < size rp by smt ()) => //=.
      (* Addition gate *)
      move => gid c; progress.
      rewrite !nth_cat /= size_cat /=.
      (have ->: gid < size rp + 1 by smt()) => //=.
      by (have ->: gid < size rp by smt ()) => //=.
      by rewrite H4 //=.
      by rewrite H5 //=. 
      (* Multiplication gate *)
      move => gid wl wr; progress.
      congr.
        rewrite !nth_cat /= size_cat /=.
        (have ->: gid < size rp + 1 by smt()) => //=.
        by (have ->: gid < size rp by smt ()) => //=.
        rewrite !nth_cat /= size_cat /=.
        (have ->: gid < size rp + 1 by smt()) => //=.
        (have ->: gid < size rp by smt ()) => //=.
have ->: get_gid wl < size rp + 1 by smt().
simplify.
have ->:  get_gid wl < size rp by smt().
simplify.
have ->: get_gid wr < size rp + 1 by smt().
simplify.
have ->: get_gid wr < size rp by smt().
done.

        rewrite !nth_cat /= size_cat /=.
        (have ->: gid < size rp + 1 by smt()) => //=.
        (have ->: gid < size rp by smt ()) => //=.
have ->: get_gid wl < size rp + 1 by smt().
simplify.
have ->:  get_gid wl < size rp by smt().
simplify.
have ->: get_gid wr < size rp + 1 by smt().
simplify.
have ->: get_gid wr < size rp by smt().
done.
      by rewrite H4 //=.
      by rewrite H5 //=.
    qed.

    (** Expands the **valid_circuit** predicate in the **mem_gid_range** lemma proved in the 
        *ArithmeticCircuit.ec* file *)
    lemma gid_bound k topo gg :
      valid_topology topo =>
      valid_gates topo gg =>
      mem_gid k gg => 0 <= k < topo.`npinputs + topo.`nsinputs + topo.`ngates.
    proof.
      rewrite /valid_topology /valid_gates; progress. 

      move : H4 H5 H6 H7; elim gg => //=.
      by move => w; progress => /#.
      by move => gid c; progress => /#.
      by move => gid wl wr; progress => /#.
      by move => gid wl wr; progress => /#.

      move : H4 H5 H6 H7; elim gg => //=.
      by move => w; progress => /#.
      by move => w; progress => /#.
      by move => gid wl wr; progress => /#.
      by move => gid wl wr; progress => /#.
    qed.

    (** Proves that if some gate/wire ID is in the circuit, then [get_gate] will always produce
        output *)
    lemma mem_gid_get_gate k gg :
      mem_gid k gg => get_gate gg k <> None.
    proof.  by elim gg => //; move => gid wl wr //= /#.  qed.

    (** Proves that if some gate/wire ID is not it the circuit, then [get_gate] will always 
        produce output *)
    lemma mem_gid_get_gateN k gg :
      !mem_gid k gg => get_gate gg k = None.
    proof. by elim gg => // /#. qed.

    (** Default (dummy) gate *)
    op def_gate (topo : topology_t) : gates_t = Constant (topo.`npinputs + topo.`nsinputs) fzero.

    (** Establishes an isomorphism between an honest prover’s execution and the simulator. 
        This isomorphism states that if the random values held by the prover and simulator are 
        uniformly sampled, then the honest prover execution (that uses the correct witness values)
        and the simulator (that assumes all witness values are zero) are computationally 
        indistinguishable. *)
    lemma isomorphism_eq topo gg (rp : u_t) ys rp' inst w : 
      valid_circuit {| topo = topo ; gates = gg ; out_wires = ys |} => 
      size rp = size rp' => 
      size rp = topo.`nsinputs + topo.`npinputs + topo.`ngates =>
      (forall (k : gid_t), mem_gid k gg =>
                           fsub (eval_until gg inst w k) (nth def_ui rp k).`b =
                           fsub fzero (nth def_ui rp' k).`b) =>
      (forall (k : int), 0 <= k < size rp =>
                         (nth def_ui rp k).`a = (nth def_ui rp' k).`a) =>
      (forall (k : int), 0 <= k < size rp =>
                         (nth def_ui rp k).`a' = (nth def_ui rp' k).`a') =>
      (forall (k : gid_t), mem_gid k gg => 
                           is_multiplication (odflt (def_gate topo) (get_gate gg k)) =>
                           fsub (fsub (fadd (fmul (nth def_ui rp (get_gid (as_multiplication (odflt (def_gate topo) (get_gate gg k))).`2)).`a (eval_gates (as_multiplication (odflt (def_gate topo) (get_gate gg k))).`3 inst w)) (fmul (nth def_ui rp (get_gid (as_multiplication (odflt (def_gate topo) (get_gate gg k))).`3)).`a (eval_gates (as_multiplication (odflt (def_gate topo) (get_gate gg k))).`2 inst w))) (nth def_ui rp k).`a) (nth def_ui rp k).`b' = 
                           fsub (fsub (fadd (fmul (nth def_ui rp' (get_gid (as_multiplication (odflt (def_gate topo) (get_gate gg k))).`2)).`a fzero) (fmul (nth def_ui rp' (get_gid (as_multiplication (odflt (def_gate topo) (get_gate gg k))).`3)).`a fzero)) (nth def_ui rp' k).`a) (nth def_ui rp' k).`b') =>
      gen_z rp  gg inst w = gen_z_sim rp' gg inst.
    proof.
      progress; move : H H2 H5; elim gg => //=.
      (* Public input gate *)
      by move => wid /#.
      (* Secret input gate *)
      by move => wid /#.
      (* Constant gate *)
      by move => gid c /#.
      (* Addition gate *)
      move => gid wl wr Hl Hr Hvalid Hind Hind2; split; first by smt().
split; first by rewrite Hl => //= /#.
      rewrite Hr => //=; first 2 by smt(). 
      progress; move : (Hind2 k).
      (have ->: gid = k <=> false by smt()) => //=.
      (have ->: mem_gid k wl <=> false by smt()) => //=.
      (have ->: get_gate wl k <> None <=> false by rewrite mem_gid_get_gateN => /#) => //=.
      by rewrite H H2 /=.
      (* Multiplication gate *)
      move => gid wl wr Hl Hr Hvalid Hind Hind2; split.
        congr; first by move : (Hind gid) => /=; rewrite mulf0.
        by rewrite !H3; move : Hvalid; rewrite /valid_circuit /valid_gates /valid_topology /=; smt.
        by move : (Hind2 gid) => /=.
      split; first by rewrite Hl => //= /#.
      rewrite Hr => //=; first 2 by smt(). 
      progress; move : (Hind2 k).
      (have ->: gid = k <=> false by smt()) => //=.
      (have ->: mem_gid k wl <=> false by smt()) => //=.
      (have ->: get_gate wl k <> None <=> false by rewrite mem_gid_get_gateN => /#) => //=.
      by rewrite H H2 /=.
    qed.

    (** We write a concrete randomness generator for the prover. It receives as input the
        prover input and it will sample [topo.`npinputs + topo.`nsinputs + topo.`ngates] random
        [a], [a'], [b] and [b'] values, where [topo] is the topology of the circuit. It will then
        generate two more sets of random [a], [a'], [b] and [b'] values for the constant and 
        multiplication gates that are appended to the circuit using the [add_final_mul] operator.
        Note that, for the last value of [a], we are restricting the probability distribution 
        into sampling from the finite field except for the value 0. *)
(*    op process_rand r gg =
      with gg = PInput wid => 
        take wid r ++ [nth def_ui r wid] ++ drop (wid+1) r
      with gg = SInput wid => 
        take wid r ++ [nth def_ui r wid] ++ drop (wid+1) r
      with gg = Constant gid c =>
        take gid r ++ [nth def_ui r gid] ++ drop (gid+1) r
      with gg = Addition gid wl wr => 
        let gid_l = get_gid wl in
        let gid_r = get_gid wr in
        take gid (process_rand r wl) ++ [{| a = fadd (nth def_ui r gid_l).`a (nth def_ui r gid_r).`a ; 
           b = fadd (nth def_ui r gid_l).`b (nth def_ui r gid_r).`b ; 
           a' = (nth def_ui r gid).`a' ; b' = (nth def_ui r gid).`b' |}] ++
        drop (gid+1) (process_rand r wr)
      with gg = Multiplication gid wl wr => 
        take gid (process_rand r wl) ++ [nth def_ui r gid] ++ drop (gid+1) (process_rand r wr).

op process_rand' r gg =
map (fun k => if is_addition (oget (get_gate gg k)) then 
                 let (gid, wl, wr) = as_addition (oget (get_gate gg k)) in
                 {| a = fadd (nth def_ui r (get_gid wl)).`a (nth def_ui r (get_gid wr)).`a ;
                    b = fadd (nth def_ui r (get_gid wl)).`b (nth def_ui r (get_gid wr)).`b ;
                    a' = (nth def_ui r k).`a' ;
                    b' = (nth def_ui r k).`b' ; |}
              else nth def_ui r k) (iota_ 0 (size r)).

lemma process_rand_size' r gg :
  size (process_rand' r gg) = size r.
proof.
rewrite /process_rand' //=.
rewrite size_map //=.
smt.
qed.

    lemma valid_rand_prover_process_rand topo gg rp :
      valid_topology topo =>
      valid_gates topo gg =>
      size rp = topo.`npinputs + topo.`nsinputs + topo.`ngates =>
      valid_rand_prover' (process_rand' rp gg) gg.
proof.
rewrite /process_rand' //=.
progress.
move : H H0.
elim gg => //=.

admit.

progress.
smt.


progress.
rewrite (nth_map witness def_ui).
smt.
simplify.
rewrite nth_iota //=.
smt.
simplify.
rewrite (nth_map witness def_ui).
move : H3.
rewrite /valid_gates //=.
progress.
smt.
smt.
simplify.
rewrite nth_iota //=.
move : H3.
rewrite /valid_gates //=.
progress.
smt.
smt.
simplify.
have ->: g = get_gid g0 <=> false.
move : H3.
rewrite /valid_gates //=.
progress.
smt.
simplify.



smt.
simplify.
rewrite (nth_map witness def_ui).
move : H3.
rewrite /valid_gates //=.
progress.
smt.
smt.
simplify.











lemma process_rand_size topo r gg :
  valid_topology topo =>
  valid_gates topo gg =>
  size r = topo.`npinputs + topo.`nsinputs + topo.`ngates =>
  size (process_rand r gg) = size r.
proof. 
rewrite /valid_topology /valid_gates //=.
progress.
move :  H4 H5 H6.
elim gg => //=.

move => wid; progress.
rewrite !size_cat //=.
rewrite !size_take //=.
have ->: wid < size r.
smt().
simplify.
smt.

move => wid; progress.
rewrite !size_cat //=.
rewrite !size_take //=.
smt().
have ->: wid < size r.
smt().
simplify.
smt.

move => gid c; progress.
rewrite !size_cat //=.
rewrite !size_take //=.
smt().
have ->: gid < size r.
smt().
simplify.
smt.

move => gid wl wr; progress.
rewrite !size_cat //=.
rewrite !size_take //=.
smt().
rewrite H4.
smt().
smt().
smt().
have ->: gid < size r.
smt().
simplify.
smt.

move => gid wl wr; progress.
rewrite !size_cat //=.
rewrite !size_take //=.
smt().
rewrite H4.
smt().
smt().
smt().
have ->: gid < size r.
smt().
simplify.
smt.
qed.


    lemma valid_rand_prover_process_rand topo gg rp :
      valid_topology topo =>
      valid_gates topo gg =>
      size rp = topo.`npinputs + topo.`nsinputs + topo.`ngates =>
      valid_rand_prover' (process_rand rp gg) gg.
proof.
rewrite /valid_topology //=.
rewrite /valid_gates //=.
progress.      
move : H4 H5 H6.
elim gg => //=.
move => gid wl wr; progress.

rewrite !nth_cat //=.
rewrite !size_cat //=.
rewrite size_take //=.
smt().
have ->: size (process_rand rp wl) = topo.`npinputs + topo.`nsinputs + topo.`ngates.
smt(process_rand_size).
rewrite !H12 //=.
have ->: gid < gid + 1 by smt().
simplify.
have ->: get_gid wl < gid + 1 by smt().
simplify.
have ->: get_gid wl < gid by smt().
simplify.
have ->: get_gid wr < gid + 1 by smt().
simplify.
have ->: get_gid wr < gid by smt().
simplify.
rewrite !nth_take //=.
smt().
smt().
admit.

rewrite !nth_cat //=.
rewrite !size_cat //=.
rewrite size_take //=.
smt().
have ->: size (process_rand rp wl) = topo.`npinputs + topo.`nsinputs + topo.`ngates.
smt(process_rand_size).
rewrite !H12 //=.
have ->: gid < gid + 1 by smt().
simplify.
have ->: get_gid wl < gid + 1 by smt().
simplify.
have ->: get_gid wl < gid by smt().
simplify.
have ->: get_gid wr < gid + 1 by smt().
simplify.
have ->: get_gid wr < gid by smt().
simplify.
rewrite !nth_take //=.
smt().
smt().
admit.
smt.


smt.


case (gid < size (process_rand rp wl)); last first; progress.
have ->: gid < size (process_rand rp wl) + 1 <=> false.
smt().
simplify.
have ->: get_gid wl < size (process_rand rp wl) + 1.
smt().
simplify.
have ->: get_gid wl < size (process_rand rp wl) by smt().
simplify.
have ->: get_gid wr < size (process_rand rp wl) + 1 by smt().
simplify.
have ->: get_gid wr < size (process_rand rp wl) by smt().
simplify.
smt.


have : size (process_rand rp gg) = topo.`npinputs + topo.`nsinputs + topo.`ngates.
rewrite (process_rand_size topo gg rp).
smt().
smt().
smt().
smt().
move : H6 H5 H4.
elim gg => //=.
move => gid wl wr; progress.
rewrite !nth_cat //=.
rewrite !size_cat //=.
rewrite size_take //=.
smt().
move : H21.
rewrite !size_cat //=.
rewrite !size_take //=.
smt().
rewrite size_drop //=.
smt().
simplify.
rewrite (process_rand_size topo wl rp).
smt().
smt().
smt().
rewrite (process_rand_size topo wr rp).
smt().
smt().
smt().
rewrite !H7 !H8 //=.
rewrite !lez_maxr.
smt().
progress.
have ->: gid < gid + 1 by smt().
simplify.
have ->: get_gid wl < gid + 1 by smt().
simplify.
have ->: get_gid wl < gid by smt().
simplify.
have ->: get_gid wr < gid + 1 by smt().
simplify.
have ->: get_gid wr < gid by smt().
simplify.
rewrite !nth_take //=.
smt().
smt().

smt.

have ->: size (process_rand rp wl) = size rp.
rewrite (process_rand_size).








rewrite /process_rand //=.
rewrite !(nth_map witness def_ui).
rewrite size_iota //=.
smt().
rewrite size_iota //=.
smt().
rewrite size_iota //=.
smt().
simplify.
rewrite !nth_iota //=.
smt().
smt().
smt().
simplify.
have ->: gid = get_gid wl <=> false by smt().
simplify.
have ->: get_gate wl (get_gid wl) <> None.
smt().
simplify.
have ->: gid = get_gid wr <=> false by smt().
simplify.
have ->: get_gate wl (get_gid wr) <> None <=> false.
admit.
simplify.
have ->: (oget (get_gate wl (get_gid wl))) = wl.
admit.
have ->: (oget (get_gate wr (get_gid wr))) = wr.
admit.
move : H4; rewrite H15 H17 H19.
move : H5; rewrite H16 H18 H20.
simplify.
rewrite /process_rand //=.
progress.


rewrite (nth_map witness def_ui).
rewrite size_iota //=.
smt().
simplify.
rewrite !nth_iota //=.
smt().
have ->: gid = get_gid wl <=> false by smt().
simplify.
have ->: get_gate wl (get_gid wl) <> None.
smt().
simplify.


have ->: gid = get_gid wr <=> false.
smt().
simplify.
have ->: get_gate wl (get_gid wr) <> None <=> false.
admit.
simplify.
case (is_addition (oget (get_gate wl (get_gid wl)))); progress.
case (is_addition (oget (get_gate wr (get_gid wr)))); progress.
admit.
smt.
smt.
smt().
case ()
admit.
admit.*)

    module RP : RandP_t = {
      proc gen(x : statement_t) : prover_rand_t = {
        var c, inst, topo, gg, rp;
        var a, b, a', b';
        var a_final_const, b_final_const, a'_final_const, b'_final_const;
        var a_final_mul, b_final_mul, a'_final_mul, b'_final_mul;
        var i;
        
        (c, inst) <- x;
        topo <- c.`topo;
        gg <- c.`gates;

        rp <- [];

        i <- 0;
        while (i < topo.`npinputs + topo.`nsinputs + topo.`ngates) {
          a <$ (FDistr.dt \ ((=)fzero));
          b <$ FDistr.dt;
          a' <$ FDistr.dt;
          b' <$ FDistr.dt;
          rp <- rp ++ [{| a = a ; b = b ; a' = a' ; b' = b' |}];
  
          i <- i + 1;
        }
        (*rp <- process_rand rp gg;*)

        (* sample randomness for final constant gate *)
        a_final_const <$ (FDistr.dt \ ((=)fzero));
        b_final_const <$ FDistr.dt;
        a'_final_const <$ FDistr.dt;
        b'_final_const <$ FDistr.dt;

        rp <- rp ++ [{| a = a_final_const ; b = b_final_const ; a' = a'_final_const ; b' = b'_final_const |}];

        (* sample randomness for final multiplication gate *)
        a_final_mul <$ (FDistr.dt \ ((=)fzero));
        b_final_mul <$ FDistr.dt;
        a'_final_mul <$ FDistr.dt;
        b'_final_mul <$ FDistr.dt;

        rp <- rp ++ [{| a = a_final_mul ; b = b_final_mul ; a' = a'_final_mul ; b' = b'_final_mul |}];

        return rp;
      }
    }.

    (** Simulator module. The simulator will behave according to the [commit] operation, but
        it will invoke the [gen_z_sim] operator (that assumes that all witness values are 0)
        instead of the honest [gen_z] operator *)
    module Simulator = {
      var x : statement_t
      proc init(x_ : statement_t) : unit = {
        x <- x_;
      }
      proc gen_commitment() : commitment_t option = {
        var c, inst, topo, gg, z, z', rp;

        (c, inst) <- x;
        rp <@ RP.gen(x);
        c <- add_final_mul c;
        topo <- c.`topo;
        gg <- c.`gates;
        z <- gen_z_sim rp gg inst;
        z' <- (get_a rp gg);

        return Some (z, z');
      }
    }.

    (** Proves that if a multiplication gate is valid, then the left wire is also going to be 
        valid *)
    lemma valid_gates_multiplication_wl topo gg k : 
      valid_topology topo => 
      valid_gates topo gg => 
      is_multiplication (odflt (def_gate topo) (get_gate gg k)) =>
      valid_gates topo (as_multiplication (odflt (def_gate topo) (get_gate gg k))).`2.
    proof.
      case (get_gate gg k = None); progress; first 3 by
        by move : H2; rewrite H /= /def_gate /=.
      by move : H H1 H2; elim gg => // /#.
      by move : H H1 H2; elim gg => // /#.
      by move : H H1 H2; elim gg => // /#.
    qed.

    (** Proves that if a multiplication gate is valid, then the right wire is also going to be 
        valid *)
    lemma valid_gates_multiplication_wr topo gg k : 
      valid_topology topo => 
      valid_gates topo gg => 
      is_multiplication (odflt (def_gate topo) (get_gate gg k)) =>
      valid_gates topo (as_multiplication (odflt (def_gate topo) (get_gate gg k))).`3.
    proof.
      case (get_gate gg k = None); progress; first 3 by
        by move : H2; rewrite H /= /def_gate /=.
      by move : H H1 H2; elim gg => // /#.
      by move : H H1 H2; elim gg => // /#.
      by move : H H1 H2; elim gg => // /#.
    qed.

    (** Proves that if a multiplication gate is valid, then the left wire ID is smaller than the
        multiplication gate ID *)
    lemma multiplication_wl_gid_bound topo gg k : 
      valid_topology topo => 
      valid_gates topo gg => 
      is_multiplication (odflt (def_gate topo) (get_gate gg k)) =>
      get_gid (as_multiplication (odflt (def_gate topo) (get_gate gg k))).`2 < k.
    proof.
      case (get_gate gg k = None); progress; first by move : H2; rewrite H /= /def_gate /=.
      by move : H H1 H2; elim gg => // /#.
    qed.

    (** Proves that if a multiplication gate is valid, then the right wire ID is smaller than the
        multiplication gate ID *)
    lemma multiplication_wr_gid_bound topo gg k : 
      valid_topology topo => 
      valid_gates topo gg => 
      is_multiplication (odflt (def_gate topo) (get_gate gg k)) =>
      get_gid (as_multiplication (odflt (def_gate topo) (get_gate gg k))).`3 < k.
    proof.
      case (get_gate gg k = None); progress; first by move : H2; rewrite H /= /def_gate /=.
      by move : H H1 H2; elim gg => // /#.
    qed.

    (** Distinguisher declaration *)    
    declare module D <: Distinguisher_t{-RealEvaluator, -Simulator, -IdealEvaluator}.
    (** Malicious verifier declaration *)    
    declare module MV <: MVerifier_t{-D, -RealEvaluator, -Simulator, -IdealEvaluator}.

    (** Zero-knowledge lemma, according to the zero-knowledge game of the 
        *ZeroKnowledgeDVNIZKP.ec* file. We prove that if the witness and the statement are in the
        relation, and if the circuit and inputs are well-formed, then the *real* workd and the
        *ideal* world are indistinguishable *)
    lemma zero_knowledge_eq &m :
      equiv [ GameReal(D, RP, MV).main ~ GameIdeal(D, MV, Simulator).main : 
                ={glob RP, glob D, glob MV} ==> ={res} ].
    proof.
      proc; inline *.
seq 1 1 : (#pre /\ ={xp, xv}).
call (_ : true); skip; progress.
sp.
if => //=; last first.
by call (_ : true).
      sp 7 12 => //=.
      seq 3 3 : (#pre /\ size rp0{2} = topo0{2}.`npinputs + topo0{2}.`nsinputs + topo0{2}.`ngates /\ 
                  size rp0{1} = size rp0{2} /\ ={i} /\ 
                  i{2} = topo0{2}.`npinputs + topo0{2}.`nsinputs + topo0{2}.`ngates /\
                  (* b isomorphism *)
                  (forall (k : gid_t), 
                     mem_gid k gg0{2} =>
                     fsub (eval_until gg0{2} inst{2} xp{2}.`1 k) (nth def_ui rp0{1} k).`b =
                     fsub fzero (nth def_ui rp0{2} k).`b) /\ 
                  (* a isomorphism *)
                  (forall (k : int), 0 <= k < size rp0{2} =>
                     (nth def_ui rp0{1} k).`a <> fzero) /\
                  (forall (k : int), 0 <= k < size rp0{2} =>
                     (nth def_ui rp0{1} k).`a = (nth def_ui rp0{2} k).`a) /\
                  (* a' isomorphism *)
                  (forall (k : int), 0 <= k < size rp0{2} =>
                     (nth def_ui rp0{1} k).`a' = (nth def_ui rp0{2} k).`a') /\
                  (* b' isomorphism *)
                  (forall (k : gid_t), 
                     mem_gid k gg0{2} => 
                     is_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k)) =>
                     fsub (fsub (fadd (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`2)).`a (eval_gates (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`3 inst{2} xp{2}.`1)) (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`3)).`a (eval_gates (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`2 inst{2} xp{2}.`1))) (nth def_ui rp0{1} k).`a) (nth def_ui rp0{1} k).`b' =
                     fsub (fsub (fadd (fmul (nth def_ui rp0{2} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`2)).`a fzero) (fmul (nth def_ui rp0{2} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`3)).`a fzero)) (nth def_ui rp0{2} k).`a) (nth def_ui rp0{2} k).`b')).
      while (#pre /\ ={i} /\ size rp0{2} = i{2} /\ size rp0{1} = size rp0{2} /\ 
             0 <= i{2} <= topo0{2}.`npinputs + topo0{2}.`nsinputs + topo0{2}.`ngates /\
             (forall k, 0 <= k < i{2} => 
                        fsub (eval_until gg0{2} inst{2} xp{2}.`1 k) (nth def_ui rp0{1} k).`b = 
                        fsub fzero (nth def_ui rp0{2} k).`b) /\ 
             (forall (k : int), 0 <= k < i{2} =>
                     (nth def_ui rp0{1} k).`a <> fzero) /\
             (forall (k : int), 0 <= k < i{2} => 
                                (nth def_ui rp0{1} k).`a = (nth def_ui rp0{2} k).`a) /\
             (forall (k : int), 0 <= k < i{2} =>
                                (nth def_ui rp0{1} k).`a' = (nth def_ui rp0{2} k).`a') /\
             (forall (k : int), 0 <= k < i{2} =>
                                is_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k)) =>
                                fsub (fsub (fadd (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`2)).`a (eval_gates (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`3 inst{2} xp{2}.`1)) (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`3)).`a (eval_gates (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`2 inst{2} xp{2}.`1))) (nth def_ui rp0{1} k).`a) (nth def_ui rp0{1} k).`b' =
                                fsub (fsub (fadd (fmul (nth def_ui rp0{2} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`2)).`a fzero) (fmul (nth def_ui rp0{2} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} k))).`3)).`a fzero)) (nth def_ui rp0{2} k).`a) (nth def_ui rp0{2} k).`b')).
        wp.
        (* b' isomorphism *)
        rnd (fun r => fsub r (fsub (fadd (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} i{2}))).`2)).`a (eval_gates (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} i{2}))).`3 inst{2} xp{2}.`1)) (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} i{2}))).`3)).`a (eval_gates (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} i{2}))).`2 inst{2} xp{2}.`1))) (nth def_ui rp0{1} i{2}).`a)) 
            (fun r => fadd r (fsub (fadd (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} i{2}))).`2)).`a (eval_gates (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} i{2}))).`3 inst{2} xp{2}.`1)) (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} i{2}))).`3)).`a (eval_gates (as_multiplication (odflt (def_gate topo0{2}) (get_gate gg0{2} i{2}))).`2 inst{2} xp{2}.`1))) (nth def_ui rp0{1} i{2}).`a)).
        rnd.
        (* b isomorphism *)
        rnd (fun r => fsub r (eval_until gg0{2} inst{2} xp{2}.`1 i{2})) 
            (fun r => fadd r (eval_until gg0{2}  inst{2} xp{2}.`1 i{2})).
        rnd.
        skip; progress; first 4 by ringeq.
          by rewrite size_cat /=.
          by rewrite !size_cat /= /#.
          by smt().
          by smt().
          rewrite !nth_cat /=.
          case (k = size rp0{2}); progress.
            (have ->: size rp0{2} < size rp0{1} <=> false by smt()) => //=.
            (have ->: size rp0{2} - size rp0{1} = 0 by smt()) => //=.
            by ringeq.
          (have ->: k < size rp0{1} <=> true by smt()) => //=.
          (have ->: k < size rp0{2} by smt()) => //=.
          by smt().

rewrite !nth_cat //=.
case (k = size rp0{1}); progress.
smt.
smt().

          rewrite !nth_cat /=.
          case (k = size rp0{2}); progress.
          (have ->: size rp0{2} < size rp0{1} <=> false by smt()) => //=.
          (have ->: size rp0{2} - size rp0{1} = 0 by smt()) => //=.
          (have ->: k < size rp0{1} <=> true by smt()) => //=.
          (have ->: k < size rp0{2} by smt()) => //=.
          by smt().
          rewrite !nth_cat /=.
          case (k = size rp0{2}); progress.
          (have ->: size rp0{2} < size rp0{1} <=> false by smt()) => //=.
          (have ->: size rp0{2} - size rp0{1} = 0 by smt()) => //=.
          (have ->: k < size rp0{1} <=> true by smt()) => //=.
          (have ->: k < size rp0{2} by smt()) => //=.
          by smt().
          rewrite !nth_cat /=.
          case (k = size rp0{2}); progress.
          case (get_gate c0{2}.`gates (size rp0{2}) = None); progress; first by smt().
          have : valid_gates c0{2}.`Circuit.topo (as_multiplication (odflt (def_gate c0{2}.`Circuit.topo) (get_gate c0{2}.`Circuit.gates (size rp0{2})))).`2. 
move : H H0.
rewrite /valid_inputs //=.
rewrite /valid_circuit //=.
smt.
          progress.
          (have ->: get_gid (as_multiplication (odflt (def_gate c0{2}.`Circuit.topo) (get_gate c0{2}.`Circuit.gates (size rp0{2})))).`2 < size rp0{1}).
move : H H0.
rewrite /valid_inputs //=.
rewrite /valid_circuit //=.
smt.
          (have ->: get_gid (as_multiplication (odflt (def_gate c0{2}.`Circuit.topo) (get_gate c0{2}.`Circuit.gates (size rp0{2})))).`3 < size rp0{1}). 
move : H H0.
rewrite /valid_inputs //=.
rewrite /valid_circuit //=.
smt.
          (have ->: size rp0{2} < size rp0{1} <=> false by smt()) => //=.
          (have ->: size rp0{2} - size rp0{1} = 0 by smt()) => //=.
          (have ->: get_gid (as_multiplication (odflt (def_gate c0{2}.`Circuit.topo) (get_gate c0{2}.`Circuit.gates (size rp0{2})))).`2 < size rp0{2} by rewrite (multiplication_wl_gid_bound c0{2}.`Circuit.topo c0{2}.`Circuit.gates (size rp0{2})) => /#) => //=. 
          (have ->: get_gid (as_multiplication (odflt (def_gate c0{2}.`Circuit.topo) (get_gate c0{2}.`Circuit.gates (size rp0{2})))).`3 < size rp0{2} by rewrite (multiplication_wr_gid_bound c0{2}.`Circuit.topo c0{2}.`Circuit.gates (size rp0{2})) => /#) => //=. 
          ringeq; first rewrite ofint0 /def_ui nth_default. smt().
smt().
          (have ->: get_gid (as_multiplication (odflt (def_gate c0{2}.`Circuit.topo) (get_gate c0{2}.`Circuit.gates k))).`2 < size rp0{1} by move : (multiplication_wl_gid_bound c0{2}.`Circuit.topo c0{2}.`Circuit.gates k) => /#) => //=.
          (have ->: get_gid (as_multiplication (odflt (def_gate c0{2}.`Circuit.topo) (get_gate c0{2}.`Circuit.gates k))).`3 < size rp0{1} by move : (multiplication_wr_gid_bound c0{2}.`Circuit.topo c0{2}.`Circuit.gates k) => /#) => //=.
          (have ->: k < size rp0{1} by smt()) => //=.
          (have ->: get_gid (as_multiplication (odflt (def_gate c0{2}.`Circuit.topo) (get_gate c0{2}.`Circuit.gates k))).`2 < size rp0{2} by move : (multiplication_wl_gid_bound c0{2}.`Circuit.topo c0{2}.`Circuit.gates k) => /#) => //=.
          (have ->: get_gid (as_multiplication (odflt (def_gate c0{2}.`Circuit.topo) (get_gate c0{2}.`Circuit.gates k))).`3 < size rp0{2} by move : (multiplication_wr_gid_bound c0{2}.`Circuit.topo c0{2}.`Circuit.gates k) => /#) => //=.
          (have ->: k < size rp0{2} by smt()) => //=.
smt().
smt().
smt().
        wp; skip; progress => //=; first 8 by smt().
          by rewrite H8; smt(mem_gid_range).
          by rewrite H12; smt(mem_gid_range).
      rcondt{1} 12.
        progress; do(wp;rnd); wp; skip; progress.
rewrite /valid_rand_prover //=.
         rewrite !size_cat /=.
have ->: xp{m0} = (xp{m0}.`1, xp{m0}.`2) by smt().
simplify.
have ->: xp{m0}.`2 = (xp{m0}.`2.`1, xp{m0}.`2.`2) by smt().
simplify.
have ->: size rp0{hr} + 2 =
xp{m0}.`2.`1.`Circuit.topo.`nsinputs + xp{m0}.`2.`1.`Circuit.topo.`npinputs +
xp{m0}.`2.`1.`Circuit.topo.`ngates + 2 by
smt().
simplify.
progress.
rewrite !nth_cat //=.
rewrite !size_cat //=.
case (k < size rp0{hr} + 1); progress.
case (k < size rp0{hr}); progress.
smt().
have ->: k - size rp0{hr} = 0 <=> true by smt().
simplify.
smt.
have ->: k - (size rp0{hr} + 1) = 0 by smt().
simplify.
smt.

(*move : H H0 H3 H6.
elim (xp{m0}) => circ inst //=; progress.
rewrite /process_rand //=.
         rewrite !size_cat /=.
rewrite size_map //=.
rewrite size_iota //=.
smt().
        rewrite !nth_cat /= !size_cat /=.
        (have ->: c{m0}.`topo.`nsinputs + c{m0}.`topo.`npinputs + c{m0}.`topo.`ngates + 1 < size rp0{hr} + 1 <=> false by smt()) => //=.
        (have ->: c{m0}.`topo.`nsinputs + c{m0}.`topo.`npinputs + c{m0}.`topo.`ngates + 1 - (size rp0{hr} + 1) = 0 by smt()) => //=.
        by move : (supp_dexcepted a_final_mul0 FDistr.dt ((=) fzero)) => /#.*)
      (*rcondt{2} 13.
        progress; do(wp;rnd); skip; progress.
        by rewrite !size_cat /= /#.
        rewrite !nth_cat /= !size_cat /=.
        (have ->: c{hr}.`topo.`nsinputs + c{hr}.`topo.`npinputs + c{hr}.`topo.`ngates + 1 < size rp0{hr} + 1 <=> false by smt()) => //=.
        (have ->: c{hr}.`topo.`nsinputs + c{hr}.`topo.`npinputs + c{hr}.`topo.`ngates + 1 - (size rp0{hr} + 1) = 0 by smt()) => //=.
        by move : (supp_dexcepted a_final_mul0 FDistr.dt ((=) fzero)) => /#.*)
      (*rcondt{2} 25; first by progress; do(wp;rnd); skip.*)
      rcondt{2} 18; first by progress; do(wp;rnd); skip.
      call (_ : true); wp; call (_ : true); wp.
      (* b' isomorphism *)
      rnd (fun r => fsub r (fsub (fadd (fmul a_final_const{2} (eval_gates c0{2}.`gates inst{2} xp{2}.`1)) (fmul (nth def_ui rp0{1} (get_gid c0{2}.`gates)).`a fone)) fzero)) 
          (fun r => fadd r (fsub (fadd (fmul a_final_const{2} (eval_gates c0{2}.`gates inst{2} xp{2}.`1)) (fmul (nth def_ui rp0{1} (get_gid c0{2}.`gates)).`a fone)) fzero)).
      (* a' isomorphism *)
      rnd (fun r => fsub r (fsub (fmul a_final_const{1} (nth def_ui rp0{2} (get_gid c0{2}.`gates)).`a) (fmul a_final_const{1} (nth def_ui rp0{2} (get_gid c0{2}.`gates)).`a))) 
          (fun r => fadd r (fsub (fmul a_final_const{2} (nth def_ui rp0{2} (get_gid c0{2}.`gates)).`a) (fmul a_final_const{1} (nth def_ui rp0{2} (get_gid c0{2}.`gates)).`a))).
      (* b isomorphism *)
      rnd (fun r => fsub r (eval_gate (get_gid c0{2}.`gates) c0{2}.`gates inst{2} xp{2}.`1)) 
          (fun r => fadd r (eval_gate (get_gid c0{2}.`gates) c0{2}.`gates inst{2} xp{2}.`1)).
      rnd; wp; rnd; rnd.
      (* b isomorphism *)
      rnd (fun r => fsub r fone) (fun r => fadd r fone).
      rnd; skip; progress; first 8 by ringeq.
smt().
        rewrite /commit /get_a /= /add_final_mul /= !nth_cat /= !size_cat /=.
have ->: xp{2} = (xp{2}.`1, xp{2}.`2) by smt().
simplify.
have ->: xp{2}.`2 = (xp{2}.`2.`1, xp{2}.`2.`2) by smt().
simplify.
have ->: xp{2}.`2.`1.`Circuit.topo.`npinputs + xp{2}.`2.`1.`Circuit.topo.`nsinputs +
 xp{2}.`2.`1.`Circuit.topo.`ngates + 1 =
 c0{2}.`Circuit.topo.`npinputs + c0{2}.`Circuit.topo.`nsinputs +
 c0{2}.`Circuit.topo.`ngates + 1.
smt().
simplify.
rewrite !nth_cat //=.
rewrite !size_cat //=.


        (have ->: c0{2}.`topo.`npinputs + c0{2}.`topo.`nsinputs + c0{2}.`topo.`ngates + 1 < size rp0{1} + 1 <=> false by smt()) => //=.
        (have ->: c0{2}.`topo.`npinputs + c0{2}.`topo.`nsinputs + c0{2}.`topo.`ngates + 1 - (size rp0{1} + 1) = 0 <=> true by smt()) => //=.
        (have ->: xp{2}.`2.`1.`Circuit.topo.`npinputs +
              xp{2}.`2.`1.`Circuit.topo.`nsinputs +
              xp{2}.`2.`1.`Circuit.topo.`ngates < size rp0{1} + 1 by smt()) => //=.
        (have ->: xp{2}.`2.`1.`Circuit.topo.`npinputs +
              xp{2}.`2.`1.`Circuit.topo.`nsinputs +
              xp{2}.`2.`1.`Circuit.topo.`ngates < size rp0{1} <=> false by smt()) => //=.
        (have ->: xp{2}.`2.`1.`Circuit.topo.`npinputs +
              xp{2}.`2.`1.`Circuit.topo.`nsinputs +
              xp{2}.`2.`1.`Circuit.topo.`ngates - size rp0{1} = 0 by smt()) => //=.
        (have ->: get_gid xp{2}.`2.`1.`gates < size rp0{1} + 1 <=> true by move : H0; rewrite /valid_inputs  /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit)) => //=.
        (have ->:get_gid xp{2}.`2.`1.`gates < size rp0{1} <=> true by move : H0; rewrite /valid_inputs /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit)) => //=.
        (have ->: c0{2}.`topo.`npinputs + c0{2}.`topo.`nsinputs + c0{2}.`topo.`ngates + 1 < size rp0{2} + 1 <=> false by smt()) => //=.
        (have ->: c0{2}.`topo.`npinputs + c0{2}.`topo.`nsinputs + c0{2}.`topo.`ngates + 1 - (size rp0{2} + 1) = 0 by smt()) => //=.
        (have ->: c0{2}.`topo.`npinputs + c0{2}.`topo.`nsinputs + c0{2}.`topo.`ngates < size rp0{2} + 1 <=> true by smt()) => //=.
        (have ->: c0{2}.`topo.`npinputs + c0{2}.`topo.`nsinputs + c0{2}.`topo.`ngates < size rp0{2} <=> false by smt()) => //=.
        (have ->: c0{2}.`topo.`npinputs + c0{2}.`topo.`nsinputs + c0{2}.`topo.`ngates - size rp0{2} = 0 <=> true by smt()) => //=.
        (have ->: get_gid c0{2}.`gates < size rp0{2} + 1 by move : H0; rewrite /valid_inputs /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit)) => //=.
        (have ->: get_gid c0{2}.`gates < size rp0{2} by move : H0; rewrite /valid_inputs /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit)) => //=.
move : H H0.
rewrite /valid_inputs //=.
have ->: xp{2} = (xp{2}.`1, xp{2}.`2) by smt().
simplify.
have ->: xp{2}.`2 = (xp{2}.`2.`1, xp{2}.`2.`2) by smt().
simplify.
progress.
congr; first by rewrite eval_gate_gid; ringeq.

by move : H; rewrite /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit).
have ->: get_gid xp{2}.`2.`1.`gates < size rp0{1} by smt().
simplify.
by ringeq.

          (*rewrite H6 /=; 
            first by move : H2; rewrite /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit).
          by ringeq.
          rewrite H6 /=; 
            first by move : H2; rewrite /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit).
          by ringeq.
          split.*) congr; first by ringeq.
have ->: get_gid xp{2}.`2.`1.`gates < size rp0{1} by smt().
simplify.

          rewrite (gen_z_cat rp0{1} xp{2}.`2.`1.`topo xp{2}.`2.`1.`gates xp{2}.`2.`1.`out_wires xp{2}.`2.`2 xp{2}.`1) 1,2:/#. 
          rewrite (gen_z_sim_cat rp0{2} xp{2}.`2.`1.`topo xp{2}.`2.`1.`gates xp{2}.`2.`1.`out_wires) 1,2:/#. 
          by rewrite (isomorphism_eq xp{2}.`2.`1.`topo xp{2}.`2.`1.`gates rp0{1} xp{2}.`2.`1.`out_wires rp0{2} xp{2}.`2.`2 xp{2}.`1) => // /#.
    qed.

    (** Another version of Zero-knowledge lemma, where we use the above equivalence lemma to
        state that both the *real* and *ideal* world security experiences end with the same
        probability distribution on their outputs *)
    lemma zero_knowledge &m :
      Pr[ GameReal(D, RP, MV).main() @ &m : res ] = 
      Pr[ GameIdeal(D, MV, Simulator).main() @ &m : res ].
    proof.  by progress; byequiv (zero_knowledge_eq &m) => //=. qed.

  end section ZeroKnowledge.

  (** Final printouts, printing a *readable* version of the completeness, soundness and 
      zero-knowledge lemmas *)
  print completeness.
  print soundness.
  print zero_knowledge.

end LPZK.
