(**
  Completness security definition for designated verifier non-interactive zero-knowledge proof
  (DVNIZKP) protocols. 

  This file formalizes the completeness cryptographic experience for DVNIZK protocols. 
  Informally, the game takes as input a witness and a statement, which is then feed to the
  protocol. The final output of the game is bit *b*, corresponding to the verifier decision.

  The game is parameterized by a randomness generator procedure, whose goal is to provide
  the appropriate random values to both the prover and the verifier. 

  The completeness theorem can be written as follows:
    forall (R <: Rand_t) (w : witness_t) (x : statement_t),
      relation w x => [ Completeness(R).main(w, x) : true ==> res ]
*)
from DVNIZK require import ADVNIZKProtocol.

theory Completeness.

  (** Cloning an abstract DVNIZK protocol. When instantiating completeness, a concrete protocol
      must be provided. *)
  clone import DVNIZKProtocol.

  (** Type of randomness generator procedures. Modules that realize this type should contain a 
      **gen** function that takes no input and produces both the prover and verifier randomness *)
  module type Rand_t = {
    proc gen() : prover_rand_t * verifier_rand_t
  }.

  (** Completness cryptographic experience *)
  module Completeness(R : Rand_t) = {
    proc main(w : witness_t, x : statement_t) : bool = {
      var r_p, r_v;
      var tr, y, b;

      (r_p, r_v) <@ R.gen();

      if (valid_inputs ((w,x),x) /\ valid_rands (r_p, r_v) x /\ relation w x) {
        (tr,y) <- protocol (r_p, r_v) ((w,x), x);
        b <- (snd y);
      }
      else { b <- true; (*{0,1};*) }

      return b;
    }
  }.

end Completeness.
