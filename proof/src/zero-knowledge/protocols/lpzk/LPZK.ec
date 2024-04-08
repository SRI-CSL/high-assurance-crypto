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

from DVNIZK require import ADVNIZKPProtocol.
from DVNIZK require import Completeness Soundness ZeroKnowledge.
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

  (** Before starting the commitment computation, the prover first invokes the pre-processing 
      function dubbed [add_final_mul]. This function forces all circuits to end in a 
      multiplication gate by adding a final multiplication gate to the root of the circuit tree. 
      This small pre-processing layer was added to simplify the soundness proof *)
  op add_final_mul (c : circuit_t) : circuit_t =
    let topo = c.`topo in
    let gg = c.`gates in
    let ys = c.`out_wires in
    let max_wire = topo.`npinputs + topo.`nsinputs + topo.`ngates in
    let ntopo = {| npinputs = topo.`npinputs ; nsinputs = topo.`nsinputs ;
                   noutputs = topo.`noutputs ; ngates = topo.`ngates + 2 |} in
    let ngg = Multiplication (max_wire + 1) (Constant max_wire fone) gg in
    {| topo = ntopo ; gates = ngg ; out_wires = ys|}.

  (** Prover randomness specification *)
  (** The prover will have a list composed of four field elements (a, b, a' and b') per gate *)
  type ui_t = { a : t ; b : t ; a' : t ; b' : t }.
  (** Default value for an element of the prover randomness *)
  op def_ui : ui_t = {| a = fzero ; b = fzero ; a' = fzero ; b' = fzero |}.
  (** The type of lists of elements of type [ui_t] *)
  type u_t = ui_t list.
  (** The prover randomness is a list of elements of type [ui_t] *)
  type prover_rand_t = u_t.
  
  (** Randomness validity predicate for the prover. We consider the prover randomness to be valid
      if it has the correct number of elements and if the last [a] element of the prover 
      randomness is different than 0 *)
  op valid_rand_prover (r : prover_rand_t) (x : prover_input_t) : bool =
    let (w, st) = x in
    let (c, inst) = st in
    let topo = c.`topo in
    let gg = c.`gates in
    size r = topo.`nsinputs + topo.`npinputs + topo.`ngates + 2 /\
    (nth def_ui r (topo.`nsinputs + topo.`npinputs + topo.`ngates + 2 - 1)).`a <> fzero.

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
    let alpha = rv.`alpha in let y = rv.`y in
    size y = size rp /\
    forall k, 0 <= k < size y => 
      (nth def_yi y k).`v = fadd (fmul alpha (nth def_ui rp k).`a) (nth def_ui rp k).`b /\
      (nth def_yi y k).`v' = fadd (fmul alpha (nth def_ui rp k).`a') (nth def_ui rp k).`b'.

  (** Prover output type. At the end of the protocol, the prover has no output *)
  type prover_output_t = unit. 
  (** Verifier output type. At the end of the protocol, the verifier outputs a boolean, stating
      if it accepts the proof or not *)
  type verifier_output_t = bool.

  (** Commitment type for individual gates. For each circuit gate, the prover commits values 
      [m], [m'] and [c], captured by the [zi_t] record type *)
  type zi_t = { m : t ; m' :  t ; c : t }.

  (** We model the commitment message as a tree, following the same format used for the 
      definition of arithmetic circuits *)
  type z_t = [
    | PInputZ of wid_t & zi_t
    | SInputZ of wid_t & zi_t
    | ConstantZ of gid_t & zi_t
    | AdditionZ of gid_t & zi_t & z_t & z_t
    | MultiplicationZ of gid_t & zi_t & z_t & z_t
  ].
  
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
      AdditionZ gid {| m = fzero ; m' = fzero ; c = fzero |} (gen_z u wl xp xs) (gen_z u wr xp xs)

    with gg = Multiplication gid l r => 
      let wl = eval_gates l xp xs in
      let wr = eval_gates r xp xs in
      let w = fmul wl wr in

      let ui = nth def_ui u gid in
      let ai = ui.`a in let ai' = ui.`a' in
      let bi = ui.`b in let bi' = ui.`b' in

      let ul = nth def_ui u (get_gid l) in
      let al = ul.`a in let al' = ui.`a' in

      let ur = nth def_ui u (get_gid r) in
      let ar = ur.`a in let ar' = ur.`a' in

      MultiplicationZ gid {| m = fsub w bi ; 
                             m' = fsub (fmul al ar) ai' ; 
                             c = fsub (fsub (fadd (fmul al wr) (fmul ar wl)) ai) bi' |}
                          (gen_z u l xp xs) (gen_z u r xp xs).

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
  op commit (r : prover_rand_t) (x : prover_input_t) = 
    let (w, st) = x in
    let (c, inst) = st in
    let c = add_final_mul c in
    let topo = c.`topo in
    let gg = c.`gates in
    
    let z = gen_z r gg inst w in
    let z' = (get_a r gg) in
    (z, z').

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

      AdditionF {| e = fadd (get_e fl) (get_e fr) ; e' = fzero ; e'' = fzero |} fl fr

    with z = MultiplicationZ gid zi zl zr =>
      let fl = gen_f r zl in
      let fr = gen_f r zr in

      let m = zi.`m in let m' = zi.`m' in

      let alpha = r.`alpha in
      let y = nth def_yi r.`y gid in
      let v = y.`v in let v' = y.`v' in

      let el = get_e fl in
      let er = get_e fr in

      let e = fadd v m in
      let e' = fadd v' (fmul alpha m') in
      
      MultiplicationF {| e = e ; 
                         e' = e' ; 
                         e'' = fsub (fsub (fmul el er) e) (fmul alpha e') |} fl fr.

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
  lemma valid_z_gen (u : prover_rand_t) (c : circuit_t) (inst : t list) (wit : t list) :
    valid_z (gen_z u c.`gates inst wit) c. 
  proof. by elim c => topo gg => //=; rewrite /valid_z /=; elim gg => //=. qed.

  (** Prove function.

      To validate a proof, the verifier first checks that the message it received is consistent 
      with the original circuit, meaning that it will check if the prover produced a commitment 
      for the actual circuit being evaluated. If this is the case, then the verifier will compute
      [f] in order to obtain the value [e] and for the output gate using the operator 
      [get_e] and check if e it is equal to n𝛼.
  *)
  op prove (r : verifier_rand_t) (x : verifier_input_t) (c : commitment_t) : bool =
    let (z, z') = c in
    if valid_z z (add_final_mul (fst x)) then
      let f = gen_f r z in
      let n = z' in
      if (n <> fzero) then 
          get_e f = fmul n r.`alpha
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
  clone import DVNIZKPProtocol with
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
  *)
  realize correct.
    rewrite /valid_inputs /valid_rands /valid_circuit /valid_topology /valid_rand_prover 
            /valid_rand_verifier /protocol /commit /prove /relation /add_final_mul //=.
    move => [rp] rv [xp] xv => />.
    elim xp => w stp => />.
    elim xv => c inst => />.
    elim c => topo gg ys => />.
    progress.
    rewrite /valid_z /get_a /get_e //=.
    pose max_wire := topo.`npinputs + topo.`nsinputs + topo.`ngates.
    have ->: valid_z_gates (gen_z rp gg inst w) gg by move : (valid_z_gen rp {| topo = topo ; gates = gg ; out_wires = ys |} inst w).
    have ->: (nth def_ui rp (max_wire + 1)).`a <> fzero.
      rewrite /get_a /= /get_gid; clear H5 H6 H10.
      by move : H4 H7 H12; elim gg => // => /#.
    simplify.
    move : H4 H6 H5; elim gg => //=.
    (* Public input gate *)
    move => wid => />; progress.
    rewrite /eval_circuit /get_e /get_a /=.
    move : (H14 (max_wire + 1)); have ->: 0 <= max_wire + 1 && max_wire + 1 < size rv.`y by smt().
    progress; rewrite !H6.
    case (nth fzero inst wid = fzero); progress.
      rewrite H16 mulf0.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (nth def_ui rp (max_wire + 1)).`b) (fsub fzero (nth def_ui rp (max_wire + 1)).`b) = fmul (nth def_ui rp (max_wire + 1)).`a rv.`alpha by ringeq.
      by smt(@PrimeField).
      rewrite mul1f.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (nth def_ui rp (max_wire + 1)).`b) (fsub (nth fzero inst wid) (nth def_ui rp (max_wire + 1)).`b) = fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (nth fzero inst wid) by ringeq.
      have ->: fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a = fmul (nth def_ui rp (max_wire + 1)).`a rv.`alpha by ringeq.
    by rewrite non_zero_add.
    (* Secret input gate *)
    move => wid => />; progress.
    rewrite /eval_circuit /get_e /get_a /=.
    move : (H14 (max_wire + 1)); have ->: 0 <= max_wire + 1 && max_wire + 1 < size rv.`y by smt().
    progress; rewrite !H6.
    case (nth fzero w wid = fzero); progress.
      rewrite H16 mulf0.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (nth def_ui rp (max_wire + 1)).`b) (fsub fzero (nth def_ui rp (max_wire + 1)).`b) = fmul (nth def_ui rp (max_wire + 1)).`a rv.`alpha by ringeq.
      by smt(@PrimeField).
      rewrite mul1f.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (nth def_ui rp (max_wire + 1)).`b) (fsub (nth fzero w wid) (nth def_ui rp (max_wire + 1)).`b) = fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (nth fzero w wid) by ringeq.
      have ->: fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a = fmul (nth def_ui rp (max_wire + 1)).`a rv.`alpha by ringeq.
    by rewrite non_zero_add.
    (* Constant gate *)
    move => gid c => />; progress.
    rewrite /eval_circuit /get_e /get_a /=.
    move : (H14 (max_wire + 1)); have ->: 0 <= max_wire + 1 && max_wire + 1 < size rv.`y by smt().
    progress; rewrite !H15.
    case (c = fzero) => H19.
      rewrite H19 mulf0.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp (max_wire+1)).`a) (nth def_ui rp (max_wire+1)).`b) (fsub fzero (nth def_ui rp (max_wire+1)).`b) = fmul (nth def_ui rp (max_wire+1)).`a rv.`alpha by ringeq.
      by smt(@PrimeField).
      rewrite mul1f.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp (max_wire+1)).`a) (nth def_ui rp (max_wire+1)).`b) (fsub c (nth def_ui rp (max_wire+1)).`b) = fadd (fmul rv.`alpha (nth def_ui rp (max_wire+1)).`a) c by ringeq.
      have ->: fmul rv.`alpha (nth def_ui rp (max_wire+1)).`a = fmul (nth def_ui rp (max_wire+1)).`a rv.`alpha by ringeq.
    by rewrite non_zero_add.
    (* Addition gate *)
    move => gid l r; rewrite /eval_circuit /get_e /get_a /=; progress.  
    rewrite /eval_circuit /get_e /get_a /=; progress. 
    move : H4; rewrite mul1f H6 H24 H26; progress.
    move : H5; rewrite mul1f H15 H25 H27; progress.
    rewrite /get_e /=.
    move : (H14 (max_wire + 1)); have ->: 0 <= max_wire + 1 && max_wire + 1 < size rv.`y by smt().
    progress; rewrite !H28.
    case (fadd (eval_gates l inst w) (eval_gates r inst w) = fzero); progress.
      rewrite H30 mulf0.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (nth def_ui rp (max_wire + 1)).`b) (fsub fzero (nth def_ui rp (max_wire + 1)).`b) = fmul (nth def_ui rp (max_wire + 1)).`a rv.`alpha by ringeq.
      by smt(@PrimeField).
      rewrite mul1f.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (nth def_ui rp (max_wire + 1)).`b) (fsub (fadd (eval_gates l inst w) (eval_gates r inst w)) (nth def_ui rp (max_wire + 1)).`b) = fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (fadd (eval_gates l inst w) (eval_gates r inst w)) by ringeq.
      have ->: fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a = fmul (nth def_ui rp (max_wire + 1)).`a rv.`alpha by ringeq.
    by rewrite non_zero_add.
    (* Multiplication gate *)
    move => gid l r; rewrite /eval_circuit /get_e /get_a /=; progress.  
    rewrite /eval_circuit /get_e /get_a /=; progress. 
    move : H4; rewrite H6 H24 H26; progress.
    move : H5; rewrite H15 H25 H27; progress.
    rewrite /get_e /=.
    move : (H14 (max_wire + 1)); have ->: 0 <= max_wire + 1 && max_wire + 1 < size rv.`y by smt().
    progress; rewrite !H28.
    case (fmul (eval_gates l inst w) (eval_gates r inst w) = fzero); progress.
      rewrite H30 mulf0.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (nth def_ui rp (max_wire + 1)).`b) (fsub fzero (nth def_ui rp (max_wire + 1)).`b) = fmul (nth def_ui rp (max_wire + 1)).`a rv.`alpha by ringeq.
      by smt(@PrimeField).
      rewrite mul1f.
      have ->: fadd (fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (nth def_ui rp (max_wire + 1)).`b) (fsub (fmul (eval_gates l inst w) (eval_gates r inst w)) (nth def_ui rp (max_wire + 1)).`b) = fadd (fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a) (fmul (eval_gates l inst w) (eval_gates r inst w)) by ringeq.
      have ->: fmul rv.`alpha (nth def_ui rp (max_wire + 1)).`a = fmul (nth def_ui rp (max_wire + 1)).`a rv.`alpha by ringeq.
    by rewrite non_zero_add.
  qed.

  (** Completeness proof *)
  (** First, we import the completeness security definition instantiated with LPZK *)
  clone import Completeness as LZPKCompleteness with
    theory DVNIZKPProtocol <- DVNIZKPProtocol.

  section Completeness.

    (** Randomness generator declaration *)
    declare module R <: Rand_t.
    (** Assumes that the randomness generator always terminates *)
    axiom r_gen_ll : islossless R.gen.

    (** Proves the desired completness lemma, according to the completeness game of the
        *CompletenessDVNIZKP.ec* file: we prove that, if the witness and the statement are in the
        relation, then the LPZK protocol will always produce true. The proof is done by using
        the correctness proof above. *)
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
  (** First, we import the soundness security definition instantiated with LPZK *)
  clone import Soundness as LPZKSoundness with
    theory DVNIZKPProtocol <- DVNIZKPProtocol.

  section Soundness.

    (** We write a concrete randomness generator for the verifier. It receives as input the
        prover randomness, samples a value 𝛼 at random and then computes the correct
        correlated randomness in accordance with the dealer algorithm *)
    module RV : RandV_t = {
      proc gen(rp : prover_rand_t) : verifier_rand_t = {
        var alpha, y;

        alpha <$ FDistr.dt;
        y <- map (fun u => {| v = fadd (fmul alpha u.`a) u.`b ; 
                              v' = fadd (fmul alpha u.`a') u.`b' |}) rp;

        return ({| alpha = alpha; y = y  |});
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
                                 Pr [ Soundness(RV, MP).main(rp_, x_) @ &m : res ] <= 1%r / q%r.
    proof.
      progress; byphoare (_ : rp = rp_ /\ x = x_ ==> res) => //=.
      proc; inline*.
      rcondt 6.
        wp; rnd; wp; call (_ : true); wp; skip; progress.
          by simplify; rewrite size_map //=.
          by rewrite (nth_map def_ui def_yi); first by move : H1; rewrite size_map.
          by rewrite (nth_map def_ui def_yi); move : H1; rewrite size_map.
      wp; rnd; wp; simplify; call (mp_commit_exec rp_ x_); skip; progress.
      case (! language x{hr}); progress; last by rewrite mu0; smt.
      rewrite /prove /=.
      move : H H0.
      elim result => z n /=.
      elim (x{hr}) => c inst. 
      elim c => topo gg ys /=.
      progress.
      rewrite /add_final_mul /= /valid_z /= /get_e /get_fi /=.
      pose max_wire := topo.`npinputs + topo.`nsinputs + topo.`ngates.
      case (valid_z_gates (gen_z rp{hr} gg inst w) gg); progress; last by rewrite mu0; smt.
      case (n <> fzero); progress; last by rewrite mu0; smt.
      rewrite mul1f /=.
      case (0 <= max_wire+1 < size rp{hr}); progress; last first.
        have ->: (fun (x : t) => fadd (nth def_yi (map (fun (u : ui_t) => {| v = fadd (fmul x u.`a) u.`b; v' = fadd (fmul x u.`a') u.`b'; |}) rp{hr}) (max_wire+1)).`v (fsub (eval_gates gg inst w) (nth def_ui rp{hr} (max_wire + 1)).`b) = fmul n x) = (fun (x : t) => fadd (def_yi).`v (fsub (eval_gates gg inst w) (nth def_ui rp{hr} (max_wire + 1)).`b) = fmul n x).
        rewrite fun_ext /(==); progress.
        case (!(0 <= max_wire)); progress; first by smt.
        by rewrite nth_default; first by rewrite size_map; smt().
        rewrite /def_yi /= add0f.
        have ->: mu FDistr.dt (fun (x : t) => fsub (eval_gates gg inst w) (nth def_ui rp{hr} (max_wire + 1)).`b = fmul n x) = mu1 FDistr.dt (fdiv (fsub (eval_gates gg inst w) (nth def_ui rp{hr} (max_wire + 1)).`b) n).
          by congr; rewrite fun_ext /(==); progress; smt(@PrimeField).
        by rewrite FDistr.dt1E.
      have ->: (fun (x : t) => fadd (nth def_yi (map (fun (u : ui_t) => {| v = fadd (fmul x u.`a) u.`b; v' = fadd (fmul x u.`a') u.`b'; |}) rp{hr}) (max_wire + 1)).`v (fsub (eval_gates gg inst w) (nth def_ui rp{hr} (max_wire + 1)).`b) = fmul n x) = (fun (x : t) => fadd ((fun (u : ui_t) => {| v = fadd (fmul x u.`a) u.`b; v' = fadd (fmul x u.`a') u.`b'; |}) (nth def_ui rp{hr} (max_wire + 1))).`v (fsub (eval_gates gg inst w) (nth def_ui rp{hr} (max_wire + 1)).`b) = fmul n x).
        by rewrite fun_ext /(==); progress; rewrite (nth_map def_ui def_yi).
      simplify.
      pose m := (fsub (eval_gates gg inst w) (nth def_ui rp{hr} (max_wire + 1)).`b).
      case ((nth def_ui rp{hr} (max_wire + 1)).`a = fzero); progress.
        rewrite H4 /=.
        have ->: (fun (x : t) => fadd (fadd (fmul x fzero) (nth def_ui rp{hr} (max_wire + 1)).`b) m = fmul n x) = (fun (x : t) => fadd (nth def_ui rp{hr} (max_wire + 1)).`b m = fmul n x).
          by rewrite fun_ext /(==); progress; rewrite mulf0 add0f.
        case ((nth def_ui rp{hr} (max_wire + 1)).`b = fzero); progress.
          rewrite H5 /=.
          have ->: (fun (x : t) => fadd fzero m = fmul n x) = (fun (x : t) => m = fmul n x)
            by rewrite fun_ext /(==); smt(@PrimeField). 
          have ->: mu FDistr.dt (fun (x : t) => m = fmul n x) = mu FDistr.dt (fun (x : t) => x = fdiv m n).
            rewrite (mu_eq _ (fun (x : t) => m = fmul n x) (transpose (=) (fdiv m n))).
              by rewrite /(==); progress; rewrite div_def; smt(@PrimeField).
            by done.
          have ->: mu FDistr.dt (transpose (=) (fdiv m n)) = mu1 FDistr.dt (fdiv m n) by done.
          by rewrite FDistr.dt1E.
        have ->: mu FDistr.dt (fun (x : t) => fadd (nth def_ui rp{hr} (max_wire + 1)).`b m = fmul n x) = mu FDistr.dt ((pred1) (fdiv (fadd (nth def_ui rp{hr} (max_wire + 1)).`b m) n)).
          by congr; rewrite fun_ext /(==); progress; smt(@PrimeField).
        by rewrite FDistr.dt1E.
      case ((nth def_ui rp{hr} (max_wire + 1)).`b = fzero); progress.
        rewrite H5 /=.
        case (m = fzero); progress.
          have : eval_gates gg inst w = fzero by smt(@PrimeField).
          progress; move : H.
          by rewrite /language /relation /eval_circuit /= /#.
        case ((nth def_ui rp{hr} (max_wire + 1)).`a = n); progress; first by rewrite mu0_false; progress; smt.
        have ->: mu FDistr.dt (fun (x : t) => fadd (fadd (fmul x (nth def_ui rp{hr} (max_wire + 1)).`a) fzero) m = fmul n x) = mu FDistr.dt ((pred1) (fdiv m (fsub n (nth def_ui rp{hr} (max_wire + 1)).`a))).
          by congr; rewrite fun_ext /(==); progress; smt(@PrimeField).
        by rewrite FDistr.dt1E. 
      case ((nth def_ui rp{hr} (max_wire + 1)).`a = n); progress.
        case (m = fzero); progress.
          by rewrite mu0_false; smt.
        rewrite /m.
        have ->: mu FDistr.dt (fun (x : t) => fadd (fadd (fmul x (nth def_ui rp{hr} (max_wire + 1)).`a) (nth def_ui rp{hr} (max_wire + 1)).`b) (fsub (eval_gates gg inst w) (nth def_ui rp{hr} (max_wire + 1)).`b) = fmul (nth def_ui rp{hr} (max_wire + 1)).`a x) = mu FDistr.dt (fun (x : t) => (fadd (fmul x (nth def_ui rp{hr} (max_wire + 1)).`a) (eval_gates gg inst w)) = fmul (nth def_ui rp{hr} (max_wire + 1)).`a x).
          congr; rewrite fun_ext /(==); progress; smt(@PrimeField).
        move : H; rewrite /language /relation /eval_circuit /=; progress.
        by rewrite mu0_false; progress; smt.
      have ->: mu FDistr.dt (fun (x : t) => fadd (fadd (fmul x (nth def_ui rp{hr} (max_wire + 1)).`a) (nth def_ui rp{hr} (max_wire + 1)).`b) m = fmul n x) = mu FDistr.dt ((pred1) (fdiv (fadd (nth def_ui rp{hr} (max_wire + 1)).`b m) (fsub n (nth def_ui rp{hr} (max_wire + 1)).`a))).
        by congr; rewrite fun_ext /(==); progress; smt(@PrimeField).
      by rewrite FDistr.dt1E.
    qed.

  end section Soundness.

  (** Zero-knowledge proof *)
  (** First, we import the zero-knowledge security definition instantiated with LPZK *)
  clone import ZeroKnowledge as LPZKZeroKnowledge with
    theory DVNIZKPProtocol <- DVNIZKPProtocol.

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
        AdditionZ gid {| m = fzero ; m' = fzero ; c = fzero |} (gen_z_sim u wl xp) (gen_z_sim u wr xp)

      with gg = Multiplication gid l r => 
        let wl = fzero in
        let wr = fzero in
        let w = fmul wl wr in

        let ui = nth def_ui u gid in
        let ai = ui.`a in let ai' = ui.`a' in
        let bi = ui.`b in let bi' = ui.`b' in

        let ul = nth def_ui u (get_gid l) in
        let al = ul.`a in let al' = ui.`a' in

        let ur = nth def_ui u (get_gid r) in
        let ar = ur.`a in let ar' = ur.`a' in

        MultiplicationZ gid {| m = fsub w bi ; 
                               m' = fsub (fmul al ar) ai' ; 
                               c = fsub (fsub (fadd (fmul al wr) (fmul ar wl)) ai) bi' |}
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
      by rewrite H4 //=.
      by rewrite H5 //=. 
      (* Multiplication gate *)
      move => gid wl wr; progress.
      congr.
        rewrite !nth_cat /= size_cat /=.
        (have ->: gid < size rp + 1 by smt()) => //=.
        by (have ->: gid < size rp by smt ()) => //=.
        rewrite !nth_cat /= size_cat /=.
        (have ->: get_gid wl < size rp + 1 by smt()) => //=.
        (have ->: get_gid wl < size rp by smt()) => //=.
        (have ->: get_gid wr < size rp + 1 by smt()) => //=.
        (have ->: get_gid wr < size rp by smt()) => //=.
        (have ->: gid < size rp + 1 by smt()) => //=.
        by (have ->: gid < size rp by smt()) => //=.
      rewrite !nth_cat /= size_cat /=.
      (have ->: get_gid wl < size rp + 1 by smt()) => //=.
      (have ->: get_gid wl < size rp by smt()) => //=.
      (have ->: get_gid wr < size rp + 1 by smt()) => //=.
      (have ->: get_gid wr < size rp by smt()) => //=.
      (have ->: gid < size rp + 1 by smt()) => //=.
      by (have ->: gid < size rp by smt()) => //=.
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
      move => gid wl wr; progress.
      by rewrite H4 //=.
      by rewrite H5 //=. 
      (* Multiplication gate *)
      move => gid wl wr; progress.
      congr.
        rewrite !nth_cat /= size_cat /=.
        (have ->: gid < size rp + 1 by smt()) => //=.
        by (have ->: gid < size rp by smt ()) => //=.
        rewrite !nth_cat /= size_cat /=.
        (have ->: get_gid wl < size rp + 1 by smt()) => //=.
        (have ->: get_gid wl < size rp by smt()) => //=.
        (have ->: get_gid wr < size rp + 1 by smt()) => //=.
        (have ->: get_gid wr < size rp by smt()) => //=.
        (have ->: gid < size rp + 1 by smt()) => //=.
        by (have ->: gid < size rp by smt()) => //=.
      rewrite !nth_cat /= size_cat /=.
      (have ->: get_gid wl < size rp + 1 by smt()) => //=.
      (have ->: get_gid wl < size rp by smt()) => //=.
      (have ->: get_gid wr < size rp + 1 by smt()) => //=.
      (have ->: get_gid wr < size rp by smt()) => //=.
      (have ->: gid < size rp + 1 by smt()) => //=.
      by (have ->: gid < size rp by smt()) => //=.
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
      move => gid wl wr Hl Hr Hvalid Hind Hind2; split.
        rewrite Hl 1:/#; progress; move : (Hind k).
        (have ->: gid = k <=> false by smt()) => //=.
        (have ->: k = gid <=> false by smt()) => //=.
        by rewrite H /=.
        progress; move : (Hind2 k).
        (have ->: gid = k <=> false by smt()) => //=.
        (have ->: get_gate wl k <> None by smt()) => //=.
        by rewrite H H2 /=.
      rewrite Hr 1:/#; progress; move : (Hind k).
      (have ->: gid = k <=> false by smt()) => //=.
      (have ->: k = gid <=> false by smt()) => //=.
      rewrite H /=.
      by (have ->: mem_gid k wl <=> false by smt()) => //=.
      progress; move : (Hind2 k).
      (have ->: gid = k <=> false by smt()) => //=.
      (have ->: mem_gid k wl <=> false by smt()) => //=.
      (have ->: get_gate wl k <> None <=> false
        by rewrite mem_gid_get_gateN => /#) => //=.
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

    (** Simulator module. The simulator will behave according to the [commit] operation, but
        it will invoke the [gen_z_sim] operator (that assumes that all witness values are 0)
        instead of the honest [gen_z] operator *)
    module Simulator = {
      proc gen_commitment(rp : prover_rand_t, x : statement_t) : commitment_t option = {
        var c, inst, topo, gg, z, z';

        (c, inst) <- x;
        c <- add_final_mul c;
        topo <- c.`topo;
        gg <- c.`gates;
        z <- gen_z_sim rp gg inst;
        z' <- (get_a rp gg);

        return Some (z, z');
      }
    }.

    (** Distinguisher declaration *)    
    declare module D <: Distinguisher_t.
    (** Malicious verifier declaration *)    
    declare module MV <: MVerifier_t{-D}.

    (** We write a concrete randomness generator for the prover. It receives as input the
        prover input and it will sample [topo.`npinputs + topo.`nsinputs + topo.`ngates] random
        [a], [a'], [b] and [b'] values, where [topo] is the topology of the circuit. It will then
        generate two more sets of random [a], [a'], [b] and [b'] values for the constant and 
        multiplication gates that are appended to the circuit using the [add_final_mul] operator.
        Note that, for the last value of [a], we are restricting the probability distribution 
        into sampling from the finite field except for the value 0. *)
    module RP : RandP_t = {
      proc gen(xp : prover_input_t) : prover_rand_t = {
        var w, x, c, inst, topo, gg, rp;
        var a, b, a', b';
        var a_final_const, b_final_const, a'_final_const, b'_final_const;
        var a_final_mul, b_final_mul, a'_final_mul, b'_final_mul;

        var i;
        
        (w, x) <- xp;
        (c, inst) <- x;
        topo <- c.`topo;
        gg <- c.`gates;

        rp <- [];

        i <- 0;
        while (i < topo.`npinputs + topo.`nsinputs + topo.`ngates) {
          a <$ FDistr.dt;
          b <$ FDistr.dt;
          a' <$ FDistr.dt;
          b' <$ FDistr.dt;

          rp <- rp ++ [{| a = a ; b = b ; a' = a' ; b' = b' |}];
  
          i <- i + 1;
        }

        (* sample randomness for final constant gate *)
        a_final_const <$ FDistr.dt;
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

    (** Zero-knowledge lemma, according to the zero-knowledge game of the 
        *ZeroKnowledgeDVNIZKP.ec* file. We prove that if the witness and the statement are in the
        relation, and if the circuit and inputs are well-formed, then the *real* workd and the
        *ideal* world are indistinguishable *)
    lemma zero_knowledge_eq &m :
      equiv [ GameReal(D, RP, MV).main ~ GameIdeal(D, RP, MV, Simulator).main : 
                ={glob RP, glob D, glob MV, w,x} /\ 
                relation w{2} x{2} /\
                size w{2} = x{2}.`1.`topo.`nsinputs /\ size x{2}.`2 = x{2}.`1.`topo.`npinputs /\
                valid_circuit x{2}.`1 ==> ={res} ].
    proof.
      proc; inline *.
      sp 5 5 => //=.
      seq 3 3 : (#pre /\ size rp0{2} = topo{2}.`npinputs + topo{2}.`nsinputs + topo{2}.`ngates /\ 
                  size rp0{1} = size rp0{2} /\ ={i} /\ 
                  i{2} = topo{2}.`npinputs + topo{2}.`nsinputs + topo{2}.`ngates /\
                  (* b isomorphism *)
                  (forall (k : gid_t), 
                     mem_gid k gg{2} =>
                     fsub (eval_until gg{2} inst{2} w{2} k) (nth def_ui rp0{1} k).`b =
                     fsub fzero (nth def_ui rp0{2} k).`b) /\ 
                  (* a isomorphism *)
                  (forall (k : int), 0 <= k < size rp0{2} =>
                     (nth def_ui rp0{1} k).`a = (nth def_ui rp0{2} k).`a) /\
                  (* a' isomorphism *)
                  (forall (k : int), 0 <= k < size rp0{2} =>
                     (nth def_ui rp0{1} k).`a' = (nth def_ui rp0{2} k).`a') /\
                  (* b' isomorphism *)
                  (forall (k : gid_t), 
                     mem_gid k gg{2} => 
                     is_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k)) =>
                     fsub (fsub (fadd (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`2)).`a (eval_gates (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`3 inst{2} w{2})) (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`3)).`a (eval_gates (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`2 inst{2} w{2}))) (nth def_ui rp0{1} k).`a) (nth def_ui rp0{1} k).`b' =
                     fsub (fsub (fadd (fmul (nth def_ui rp0{2} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`2)).`a fzero) (fmul (nth def_ui rp0{2} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`3)).`a fzero)) (nth def_ui rp0{2} k).`a) (nth def_ui rp0{2} k).`b')).
      while (#pre /\ ={i} /\ size rp0{2} = i{2} /\ size rp0{1} = size rp0{2} /\ 
             0 <= i{2} <= topo{2}.`npinputs + topo{2}.`nsinputs + topo{2}.`ngates /\
             (forall k, 0 <= k < i{2} => 
                        fsub (eval_until gg{2} inst{2} w{2} k) (nth def_ui rp0{1} k).`b = 
                        fsub fzero (nth def_ui rp0{2} k).`b) /\ 
             (forall (k : int), 0 <= k < i{2} => 
                                (nth def_ui rp0{1} k).`a = (nth def_ui rp0{2} k).`a) /\
             (forall (k : int), 0 <= k < i{2} =>
                                (nth def_ui rp0{1} k).`a' = (nth def_ui rp0{2} k).`a') /\
             (forall (k : int), 0 <= k < i{2} =>
                                is_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k)) =>
                                fsub (fsub (fadd (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`2)).`a (eval_gates (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`3 inst{2} w{2})) (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`3)).`a (eval_gates (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`2 inst{2} w{2}))) (nth def_ui rp0{1} k).`a) (nth def_ui rp0{1} k).`b' =
                                fsub (fsub (fadd (fmul (nth def_ui rp0{2} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`2)).`a fzero) (fmul (nth def_ui rp0{2} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} k))).`3)).`a fzero)) (nth def_ui rp0{2} k).`a) (nth def_ui rp0{2} k).`b')).
        wp.
        (* b' isomorphism *)
        rnd (fun r => fsub r (fsub (fadd (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} i{2}))).`2)).`a (eval_gates (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} i{2}))).`3 inst{2} w{2})) (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} i{2}))).`3)).`a (eval_gates (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} i{2}))).`2 inst{2} w{2}))) (nth def_ui rp0{1} i{2}).`a)) 
            (fun r => fadd r (fsub (fadd (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} i{2}))).`2)).`a (eval_gates (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} i{2}))).`3 inst{2} w{2})) (fmul (nth def_ui rp0{1} (get_gid (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} i{2}))).`3)).`a (eval_gates (as_multiplication (odflt (def_gate topo{2}) (get_gate gg{2} i{2}))).`2 inst{2} w{2}))) (nth def_ui rp0{1} i{2}).`a)).
        rnd.
        (* b isomorphism *)
        rnd (fun r => fsub r (eval_until gg{2} inst{2} w0{2} i{2})) 
            (fun r => fadd r (eval_until gg{2}  inst{2} w0{2} i{2})).
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
          case (get_gate c{2}.`gates (size rp0{2}) = None); progress; first by smt().
          have : valid_gates c{2}.`topo (as_multiplication (odflt (def_gate c{2}.`topo) (get_gate c{2}.`gates (size rp0{2})))).`2 by rewrite valid_gates_multiplication_wl => //= /#. 
          progress.
          (have ->: get_gid (as_multiplication (odflt (def_gate c{2}.`topo) (get_gate c{2}.`gates (size rp0{2})))).`2 < size rp0{1} by rewrite H3 (multiplication_wl_gid_bound c{2}.`topo c{2}.`gates (size rp0{2})) => /#) => //=. 
          (have ->: get_gid (as_multiplication (odflt (def_gate c{2}.`topo) (get_gate c{2}.`gates (size rp0{2})))).`3 < size rp0{1} by rewrite H3 (multiplication_wr_gid_bound c{2}.`topo c{2}.`gates (size rp0{2})) => /#) => //=. 
          (have ->: size rp0{2} < size rp0{1} <=> false by smt()) => //=.
          (have ->: size rp0{2} - size rp0{1} = 0 by smt()) => //=.
          (have ->: get_gid (as_multiplication (odflt (def_gate c{2}.`topo) (get_gate c{2}.`gates (size rp0{2})))).`2 < size rp0{2} by rewrite (multiplication_wl_gid_bound c{2}.`topo c{2}.`gates (size rp0{2})) => /#) => //=. 
          (have ->: get_gid (as_multiplication (odflt (def_gate c{2}.`topo) (get_gate c{2}.`gates (size rp0{2})))).`3 < size rp0{2} by rewrite (multiplication_wr_gid_bound c{2}.`topo c{2}.`gates (size rp0{2})) => /#) => //=. 
          ringeq; first by rewrite ofint0 /def_ui nth_default; first by rewrite H3.
          (have ->: get_gid (as_multiplication (odflt (def_gate c{2}.`topo) (get_gate c{2}.`gates k))).`2 < size rp0{1} by move : (multiplication_wl_gid_bound c{2}.`topo c{2}.`gates k) => /#) => //=.
          (have ->: get_gid (as_multiplication (odflt (def_gate c{2}.`topo) (get_gate c{2}.`gates k))).`3 < size rp0{1} by move : (multiplication_wr_gid_bound c{2}.`topo c{2}.`gates k) => /#) => //=.
          (have ->: k < size rp0{1} by smt()) => //=.
          (have ->: get_gid (as_multiplication (odflt (def_gate c{2}.`topo) (get_gate c{2}.`gates k))).`2 < size rp0{2} by move : (multiplication_wl_gid_bound c{2}.`topo c{2}.`gates k) => /#) => //=.
          (have ->: get_gid (as_multiplication (odflt (def_gate c{2}.`topo) (get_gate c{2}.`gates k))).`3 < size rp0{2} by move : (multiplication_wr_gid_bound c{2}.`topo c{2}.`gates k) => /#) => //=.
          (have ->: k < size rp0{2} by smt()) => //=.
          by rewrite H9 => //= /#. 
        wp; skip; progress => //=; first 5 by smt().
          by rewrite H12; smt(mem_gid_range).
          by rewrite H15; smt(mem_gid_range).
      rcondt{1} 12.
        progress; do(wp;rnd); skip; progress.
        by rewrite !size_cat /= /#.
        rewrite !nth_cat /= !size_cat /=.
        (have ->: c{m0}.`topo.`nsinputs + c{m0}.`topo.`npinputs + c{m0}.`topo.`ngates + 1 < size rp0{hr} + 1 <=> false by smt()) => //=.
        (have ->: c{m0}.`topo.`nsinputs + c{m0}.`topo.`npinputs + c{m0}.`topo.`ngates + 1 - (size rp0{hr} + 1) = 0 by smt()) => //=.
        by move : (supp_dexcepted a_final_mul0 FDistr.dt ((=) fzero)) => /#.
      rcondt{2} 12.
        progress; do(wp;rnd); skip; progress.
        by rewrite !size_cat /= /#.
        rewrite !nth_cat /= !size_cat /=.
        (have ->: c{hr}.`topo.`nsinputs + c{hr}.`topo.`npinputs + c{hr}.`topo.`ngates + 1 < size rp0{hr} + 1 <=> false by smt()) => //=.
        (have ->: c{hr}.`topo.`nsinputs + c{hr}.`topo.`npinputs + c{hr}.`topo.`ngates + 1 - (size rp0{hr} + 1) = 0 by smt()) => //=.
        by move : (supp_dexcepted a_final_mul0 FDistr.dt ((=) fzero)) => /#.
      rcondt{2} 25; first by progress; do(wp;rnd); skip.
      call (_ : true); wp; call (_ : true); wp.
      (* b' isomorphism *)
      rnd (fun r => fsub r (fsub (fadd (fmul a_final_const{2} (eval_gates c{2}.`gates inst{2} w{2})) (fmul (nth def_ui rp0{1} (get_gid c{2}.`gates)).`a fone)) fzero)) 
          (fun r => fadd r (fsub (fadd (fmul a_final_const{2} (eval_gates c{2}.`gates inst{2} w{2})) (fmul (nth def_ui rp0{1} (get_gid c{2}.`gates)).`a fone)) fzero)).
      (* a' isomorphism *)
      rnd (fun r => fsub r (fsub (fmul a_final_const{1} (nth def_ui rp0{2} (get_gid c{2}.`gates)).`a) (fmul a_final_const{1} (nth def_ui rp0{2} (get_gid c{2}.`gates)).`a))) 
          (fun r => fadd r (fsub (fmul a_final_const{2} (nth def_ui rp0{2} (get_gid c{2}.`gates)).`a) (fmul a_final_const{1} (nth def_ui rp0{2} (get_gid c{2}.`gates)).`a))).
      (* b isomorphism *)
      rnd (fun r => fsub r (eval_gate (get_gid c{2}.`gates) c{2}.`gates inst{2} w0{2})) 
          (fun r => fadd r (eval_gate (get_gid c{2}.`gates) c{2}.`gates inst{2} w0{2})).
      rnd; wp; rnd; rnd.
      (* b isomorphism *)
      rnd (fun r => fsub r fone) (fun r => fadd r fone).
      rnd; skip; progress; first 8 by ringeq.
        rewrite /commit /get_a /= /add_final_mul /= !nth_cat /= !size_cat /=.
        (have ->: c{2}.`topo.`npinputs + c{2}.`topo.`nsinputs + c{2}.`topo.`ngates + 1 < size rp0{1} + 1 <=> false by smt()) => //=.
        (have ->: c{2}.`topo.`npinputs + c{2}.`topo.`nsinputs + c{2}.`topo.`ngates + 1 - (size rp0{1} + 1) = 0 <=> true by smt()) => //=.
        (have ->: c{2}.`topo.`npinputs + c{2}.`topo.`nsinputs + c{2}.`topo.`ngates < size rp0{1} + 1 by smt()) => //=.
        (have ->: c{2}.`topo.`npinputs + c{2}.`topo.`nsinputs + c{2}.`topo.`ngates < size rp0{1} <=> false by smt()) => //=.
        (have ->: c{2}.`topo.`npinputs + c{2}.`topo.`nsinputs + c{2}.`topo.`ngates - size rp0{1} = 0 by smt()) => //=.
        (have ->: get_gid c{2}.`gates < size rp0{1} + 1 <=> true by move : H2; rewrite /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit)) => //=.
        (have ->: get_gid c{2}.`gates < size rp0{1} <=> true by move : H2; rewrite /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit)) => //=.
        (have ->: c{2}.`topo.`npinputs + c{2}.`topo.`nsinputs + c{2}.`topo.`ngates + 1 < size rp0{2} + 1 <=> false by smt()) => //=.
        (have ->: c{2}.`topo.`npinputs + c{2}.`topo.`nsinputs + c{2}.`topo.`ngates + 1 - (size rp0{2} + 1) = 0 by smt()) => //=.
        (have ->: c{2}.`topo.`npinputs + c{2}.`topo.`nsinputs + c{2}.`topo.`ngates < size rp0{2} + 1 <=> true by smt()) => //=.
        (have ->: c{2}.`topo.`npinputs + c{2}.`topo.`nsinputs + c{2}.`topo.`ngates < size rp0{2} <=> false by smt()) => //=.
        (have ->: c{2}.`topo.`npinputs + c{2}.`topo.`nsinputs + c{2}.`topo.`ngates - size rp0{2} = 0 <=> true by smt()) => //=.
        (have ->: get_gid c{2}.`gates < size rp0{2} + 1 by move : H2; rewrite /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit)) => //=.
        (have ->: get_gid c{2}.`gates < size rp0{2} by move : H2; rewrite /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit)) => //=.
        split. congr; first by rewrite eval_gate_gid; ringeq.
          rewrite H6 /=; 
            first by move : H2; rewrite /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit).
          by ringeq.
          rewrite H6 /=; 
            first by move : H2; rewrite /valid_circuit /valid_topology /valid_gates /=; smt(@PrimeField @ArithmeticCircuit).
          by ringeq.
          split. congr; first by ringeq.
          rewrite (gen_z_cat rp0{1} c{2}.`topo c{2}.`gates c{2}.`out_wires inst{2} w{2}) 1,2:/#. 
          rewrite (gen_z_sim_cat rp0{2} c{2}.`topo c{2}.`gates c{2}.`out_wires) 1,2:/#. 
          by rewrite (isomorphism_eq c{2}.`topo c{2}.`gates rp0{1} c{2}.`out_wires rp0{2} inst{2} w{2}) => // /#.
    qed.

    (** Another version of Zero-knowledge lemma, where we use the above equivalence lemma to
        state that both the *real* and *ideal* world security experiences end with the same
        probability distribution on their outputs *)
    lemma zero_knowledge &m (w : witness_t) (x : statement_t) :
      valid_circuit x.`1 =>
      relation w x =>
      size w = x.`1.`topo.`nsinputs =>
      size x.`2 = x.`1.`topo.`npinputs =>
      Pr[ GameReal(D, RP, MV).main(w,x) @ &m : res ] = 
      Pr[ GameIdeal(D, RP, MV, Simulator).main(w,x) @ &m : res ].
    proof.  by progress; byequiv (zero_knowledge_eq &m) => //=. qed.

  end section ZeroKnowledge.

  (** Final printouts, printing a *readable* version of the completeness, soundness and 
      zero-knowledge lemmas *)
  print completeness.
  print soundness.
  print zero_knowledge.

end LPZK.
