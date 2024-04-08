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
  type commit_op_t = prover_rand_t -> prover_input_t -> prover_state_t * commit_t.
  op commit : commit_op_t.
  op valid_commit : commit_t -> bool.

  type challenge_t.
  type challenge_op_t = verifier_rand_t -> verifier_input_t -> commit_t -> verifier_state_t * challenge_t.
  op challenge : challenge_op_t.
  op valid_challenge : challenge_t -> bool.

  type response_t.
  type response_op_t = prover_state_t -> challenge_t -> prover_output_t * response_t.
  op response : response_op_t.
  op valid_response : response_t -> bool.

  type decide_op_t = verifier_state_t -> response_t -> verifier_output_t.
  op decide : decide_op_t.

  type sigma_protocol_t = commit_op_t * challenge_op_t * response_op_t * decide_op_t.
  (** 3-message zk protocol *)

  type trace_t = commit_t * challenge_t * response_t.

  op protocol (r : rand_t) (x : input_t) : (trace_t * output_t) option =
    let (rp, rv) = r in
    let (xp, xv) = x in
    let (stp, c) = commit rp xp in
    if (valid_commit c) then
      let (stv, ch) = challenge rv xv c in
      if (valid_challenge ch) then
        let (y1, resp) = response stp ch in
        if (valid_response resp) then
          let y2 = decide stv resp in
          Some ((c, ch, resp), (y1, y2))
        else None
      else None
    else None.

  op run_protocol (r : rand_t) (x : input_t) (prot : sigma_protocol_t) : (trace_t * output_t) option =
    let (rp, rv) = r in
    let (xp, xv) = x in
    let (commit, challenge, response, decide) = prot in
    let (stp, c) = commit rp xp in
    if (valid_commit c) then
      let (stv, ch) = challenge rv xv c in
      if (valid_challenge ch) then
        let (y1, resp) = response stp ch in
        if (valid_response resp) then
          let y2 = decide stv resp in
          Some ((c, ch, resp), (y1, y2))
        else None
      else None
    else None.

  axiom correct (r : rand_t) (x : input_t) :
    valid_rands r x =>
    valid_inputs x =>
    protocol r x <> None =>
    snd (oget (protocol r x)) = ((), relation (fst (fst x)) (snd x)).    

end SigmaProtocol.
