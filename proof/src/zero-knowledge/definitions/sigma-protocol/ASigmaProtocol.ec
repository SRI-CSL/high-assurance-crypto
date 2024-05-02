theory SigmaProtocol.

  type witness_t.
  type statement_t.
  op relation : witness_t -> statement_t -> bool.
  op language (x : statement_t) = exists w, relation w x.

  type prover_input_t = witness_t * statement_t.
  type verifier_input_t = statement_t.
  type input_t = prover_input_t * verifier_input_t.
  op valid_inputs : prover_input_t * verifier_input_t -> bool.

  type prover_rand_t.
  type verifier_rand_t.
  type rand_t = prover_rand_t * verifier_rand_t.
  op valid_rand_prover : prover_rand_t -> prover_input_t -> bool.
  op valid_rand_verifier : verifier_rand_t -> verifier_input_t -> bool.
  op valid_rands (r : rand_t) (x : input_t) : bool =
    let (rp, rv) = r in
    let (xp, xv) = x in
    valid_rand_prover rp xp /\ valid_rand_verifier rv xv.

  type prover_output_t = unit. 
  type verifier_output_t = bool.
  type output_t = prover_output_t * verifier_output_t.

  (** 3-message zk protocol *)
  type prover_state_t.
  type verifier_state_t.

  type commit_t.
  op commit : prover_rand_t -> prover_input_t -> prover_state_t * commit_t.
  op valid_commit : commit_t -> bool.

  type challenge_t.
  op challenge : verifier_rand_t -> verifier_input_t -> commit_t -> verifier_state_t * challenge_t.
  op valid_challenge : challenge_t -> bool.

  type response_t.
  op response : prover_state_t -> challenge_t -> prover_output_t * response_t.
  op valid_response : response_t -> bool.

  op decide : verifier_state_t -> response_t -> verifier_output_t.

  (** 3-message zk protocol *)

  type trace_t = commit_t * challenge_t * response_t.

  op protocol (r : rand_t) (x : input_t) : trace_t * output_t =
    let (rp, rv) = r in
    let (xp, xv) = x in
    let (stp, c) = commit rp xp in
    let (stv, ch) = challenge rv xv c in
    let (y1, resp) = response stp ch in
    let y2 = decide stv resp in
    ((c, ch, resp), (y1, y2)).

  axiom correct (r : rand_t) (x : input_t) :
    valid_rands r x =>
    valid_inputs x =>
    snd (protocol r x) = ((), relation (fst (fst x)) (snd x)).    

end SigmaProtocol.
