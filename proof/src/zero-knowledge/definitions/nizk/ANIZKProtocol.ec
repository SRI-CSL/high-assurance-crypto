theory NIZKProtocol.

  type witness_t.
  type statement_t.

  op relation : witness_t -> statement_t -> bool.
  op language (x : statement_t) = exists w, relation w x.

  type prover_input_t = witness_t * statement_t.
  type verifier_input_t = statement_t.
  op valid_inputs : prover_input_t * verifier_input_t -> bool.

  type prover_rand_t.
  type verifier_rand_t.
  op valid_rand_prover : prover_rand_t -> prover_input_t -> bool.
  op valid_rand_verifier : verifier_rand_t -> verifier_input_t -> bool.
  op valid_rands (r : prover_rand_t * verifier_rand_t) (x : prover_input_t * verifier_input_t) : bool =
    let (rp, rv) = r in
    let (xp, xv) = x in
    valid_rand_prover rp xp /\ valid_rand_verifier rv xv.  

  type prover_output_t = unit. 
  type verifier_output_t = bool.

  (** Non-interactive protocol (only one message sent from prover to verifier) *)
  type commitment_t.
  op commit : prover_rand_t -> prover_input_t -> commitment_t.

  op prove : verifier_rand_t -> verifier_input_t -> commitment_t -> bool.
  (** Non-interactive protocol (only one message sent from prover to verifier) *)

  type trace_t = commitment_t.

  op protocol (r : prover_rand_t * verifier_rand_t) 
              (x : prover_input_t * verifier_input_t) : 
              trace_t * (prover_output_t * verifier_output_t) = 
    let (r_p, r_v) = r in let (x_p, x_v) = x in
    let c = commit r_p x_p in
    let b = prove r_v x_v c in (c, ((),b)).

  axiom correct (r : prover_rand_t * verifier_rand_t) 
                (x : prover_input_t * verifier_input_t) :
    valid_inputs x =>
    valid_rands r x =>
    snd (snd (protocol r x)) = relation (fst (fst x)) (snd x). 

end NIZKProtocol.
