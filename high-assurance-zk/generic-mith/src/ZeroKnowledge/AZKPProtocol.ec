require import Distr.

from General require import Utils.

theory ZKPProtocol.

  type witness_t.
  type statement_t.
  type prover_rand_t.
  type prover_state_t.
  type commitment_t.
  type verifier_rand_t.
  type challenge_t.
  op chald : challenge_t distr.
  axiom chald_ll : is_lossless chald.

  type response_t.

  op relation : witness_t -> statement_t -> bool.
  op language(x : statement_t) = exists w, relation w x.

  type prover_input_t = witness_t * statement_t.
  type verifier_input_t = statement_t.
  op valid_inputs : prover_input_t * verifier_input_t -> bool.
  op valid_rand_verifier : verifier_rand_t -> verifier_input_t -> bool.
  op valid_rand_prover : prover_rand_t -> prover_input_t -> bool.
  op valid_rands (r : prover_rand_t * verifier_rand_t) (x : prover_input_t * verifier_input_t) : bool =
    let (rp, rv) = r in
    let (xp, xv) = x in
    valid_rand_prover rp xp /\ valid_rand_verifier rv xv.  

  type prover_output_t = unit. 
  type verifier_output_t = bool.

  type verifier_state_t = statement_t * commitment_t * challenge_t.

  op commit : prover_rand_t -> prover_input_t -> 
                               prover_state_t * commitment_t.
  op challenge : verifier_rand_t -> verifier_input_t -> 
             commitment_t -> verifier_state_t * challenge_t.
  op response   : prover_state_t -> challenge_t -> response_t.
  op check : verifier_state_t -> response_t -> bool.

  type trace_t = commitment_t * challenge_t * response_t.

  op protocol (r : prover_rand_t * verifier_rand_t) 
              (x : prover_input_t * verifier_input_t) : 
              trace_t * (prover_output_t * verifier_output_t) = 
    let (r_p, r_v) = r in let (x_p, x_v) = x in
    let (st_p,c) = commit r_p x_p in
    let (st_v,ch) = challenge r_v x_v c in
    let r = response st_p ch in
              let b = check st_v r in ((c, ch, r), ((),b)).

  axiom correct (r : prover_rand_t * verifier_rand_t) 
                (x : prover_input_t * verifier_input_t) :
    valid_inputs x =>
    valid_rands r x =>
    snd (snd (protocol r x)) = relation (fst (fst x)) (snd x).

end ZKPProtocol.
