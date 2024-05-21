(**
  Soundness security definition for designated verifier non-interactive zero-knowledge proof
  (DVNIZKP) protocols. 

  This file formalizes the soundness cryptographic experience for DVNIZK protocols. 
  The game takes as input the prover randomness and a statement, and is parameterized by a 
  malicious prover, that can maliciously generate commitments given the prover randomness and
  the statement. The soundness game will then output **1** if the statement is not part of the
  language (meaning that there is no witness that generates a positive proof for it) but the 
  verifier ends up accepting the proof either way.

  The soundness theorem can be written as follows:
    forall (R <: RandV_t) (MP <: MProver_t) (rp : prover_rand_t) (x : statement_t),
      Pr [ Soundness(RV, MP).main(rp, x) : true ==> ={res} ] <= eps,
  for any soundness error *eps*
*)
from DVNIZK require import ADVNIZKProtocol.

theory Soundness.

  (** Cloning an abstract DVNIZK protocol. When instantiating soundness, a concrete protocol
      must be provided. *)
  clone import DVNIZKProtocol.

  (** Type of randomness generator procedures. Modules that realize this type should contain a 
      **gen** function that takes as input the prover randomness and generates the correlated
      verifier randomness *)
  module type RandV_t = {
    proc gen(rp : prover_rand_t) : verifier_rand_t
  }.

  (** Malicious prover type. A malicious prover is able to produce a commitment given only the
      statement, and will try to convince the verifier into accepting the proof even with an
      invalid commitment *)
  module type MProver_t = {
    proc commit(rp : prover_rand_t, x : statement_t) : commitment_t
  }.
  
  (** Soundness cryptographic experience *)
  module Soundness(R : RandV_t, MP : MProver_t) = {
    proc main(rp : prover_rand_t, x : statement_t) : bool = {
      var b, c, rv;

      c <@ MP.commit(rp, x);

      rv <@ R.gen(rp);
      if (valid_rand_verifier rp rv x) {
        b <- !language x /\ valid_rand_prover rp x /\ prove rv x c;
      } else { b <- false; }

      return b;
    }
  }.
  
end Soundness.
