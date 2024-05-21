(**
  Syntax of a designated verifier non-interactive zero-knowledge proof (DVNIZKP) protocol.

  In the DVNIZKP model, it is assumed that input-independent *correlated* randomness has been 
  pre-processed and that the interaction between the prover and verifier consists of a single 
  message sent by the former to the latter. The terminology *designated verifier* is used to 
  attest that only a verifier holding correlated randomness with the prover is able to correctly 
  verify the proof produced by the prover.

  The syntax definition makes a mix-use of abstract and concrete types and operators. Undefined 
  data types and operators must be specified by each protocol at the instantiation step, 
  including the witness, statement and randomness types. The output types of both the prover and 
  verifier are hardwired into the formalization as a singleton and boolean value, respectively, 
  since these will be the same for each possible instantiation of a DVNIZK protocol.

  Because our formalization focuses on non-interactive protocols, we only specify one prover 
  operator - **commit** - and one verifier operator - **prove**. Informally, the prover will run 
  commit, producing a proof message that is sent to the verifier, that can then finish the ZK  
  protocol by attesting the validity of the statement by invoking **prove**. The honest protocol 
  execution is specified by the **protocol** method. Both operators are abstract, and need to be 
  realized when instantiating a concrete DVNIZK protocol. Moreover, both operators are 
  de-randomized, meaning that randomness needs to be explicitly given to both the prover and the 
  verifier. This is natural restriction, that essentially assumes that randomness is sampled 
  uniformly by some honest random generator procedure.
*)
theory DVNIZKProtocol.

  (** Witness type. This type needs to be made concrete when the protocol is instantiated *)
  type witness_t.
  (** Statement type. This type needs to be made concrete when the protocol is instantiated *)
  type statement_t.

  (** Relation. Specifies which witness and statement values produce valid/invalid proofs *)
  op relation : witness_t -> statement_t -> bool.
  (** Language. If a statement is in the *language*, then it exists an witness value that 
      produces a valid proof *)
  op language (x : statement_t) = exists w, relation w x.

  (** Prover input type. The prover starts the protocol holding the witness and the statement *)
  type prover_input_t = witness_t * statement_t.
  (** Verifier input type. The verifier starts the protocol holding the statement *)
  type verifier_input_t = statement_t.
  (** Input validity predicate. Specifies what it means for an inputs to be well-formed *)
  op valid_inputs : prover_input_t * verifier_input_t -> bool.

  (** Prover randomness type. This type needs to be made concrete when the protocol is 
      instantiated *)
  type prover_rand_t.
  (** Verifier randomness type. This type needs to be made concrete when the protocol is 
      instantiated *)
  type verifier_rand_t.
  (** Prover randomness validity predicate. Specifies what it means for an inputs to be 
      well-formed *)
  op valid_rand_prover : prover_rand_t -> statement_t -> bool.
  (** Verifier randomness validity predicate. The goal of this operator is to assure that the 
      randomness given to the verifier is *correlated* to the randomness given to the prover, and 
      represents an essential component of our formalization, since the two parties will only be 
      able to correctly execute the a DVNIZK protocol if both randomness are *correlated*. 
      Nevertheless, we do not provide a concrete specification of this predicate, since different       designated verifier protocols can have different randomness correlated assumptions. *)
  op valid_rand_verifier : prover_rand_t -> verifier_rand_t -> verifier_input_t -> bool.
  (** Randomness validity predicate. Aggregates the **valid_rand_prover** and 
      **valid_rand_verifier** predicates to specify what it means for an randomness to be 
      well-formed *)
  op valid_rands (r : prover_rand_t * verifier_rand_t) (x : statement_t) : bool =
    let (rp, rv) = r in
    valid_rand_prover rp x /\ valid_rand_verifier rp rv x.  

  (** Prover output type. At the end of the protocol, the prover has no output *)
  type prover_output_t = unit. 
  (** Verifier output type. At the end of the protocol, the verifier outputs a boolean, stating
      if it accepts the proof or not *)
  type verifier_output_t = bool.

  (** Commitment message type. This is the only message that is exchanged in a DVNIZK protocol. 
      This type needs to be made concrete when the protocol is instantiated *)
  type commitment_t.

  (** Commit operation. This operator defines how the prover computes the commitment message,
      given its input and randomness. This operator needs to be made concrete when the protocol 
      is instantiated *)
  op commit : prover_rand_t -> prover_input_t -> commitment_t.
  (** Prove operation. This operator defines how the verifier computes its decision on accepting
      the proof, given its input, randomness and the commitment message. This operator needs to 
      be made concrete when the protocol is instantiated *)
  op prove : verifier_rand_t -> verifier_input_t -> commitment_t -> bool.

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

  (** Correction assumption. Assuming that inputs and randomness values are well-formed, the 
      protocol is correct if the verifier outputs the same value given by the **relation** 
      operator. This axiom transforms in a lemma when the protocol is instantiated, and needs
      to be proven in order to correctly and fully instantiate the protocol. *)
  axiom correct (r : prover_rand_t * verifier_rand_t) 
                (x : prover_input_t * verifier_input_t) :
    valid_inputs x =>
    valid_rands r x.`1.`2 =>
    snd (snd (protocol r x)) = relation (fst (fst x)) (snd x).

end DVNIZKProtocol.
