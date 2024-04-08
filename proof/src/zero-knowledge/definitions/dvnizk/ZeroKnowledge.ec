(**
  Zero-knowledge security definition for designated verifier non-interactive zero-knowledge proof
  (DVNIZKP) protocols. 

  The zero-knowledge property is formalized by defining two experiments, typically known as the 
  *real* and *ideal* worlds. We capture both worlds with a single module **ZKGame**, which can be
  parameterized by a real-world evaluator or an ideal-world evaluator. Such an evaluator either 
  outputs a protocol execution trace or a failure symbol (represented by option). This trace is 
  given to a distinguisher, which produces a bit. Intuitively, if the two worlds are 
  indistinguishable, then the distinguisher will output 1 with essentially the same probability 
  in either one. The **Real** evaluator module animates the interaction of a malicious verifier
  **MV** with the prover. The **Ideal** evaluator module, which we omit due to space constraints,
  animates a unique interaction between a simulator and the malicious verifier. The goal of the 
  simulator is to present to the verifier a view that is indistinguishable from a real execution,
  without knowing the witness.

  The zero-knowledge theorem can be written as follows:
    forall (RP <: RandP_t) (MV <: MVerifier_t) (w : witness_t) (x : statement_t),
      | Pr [ ZKGame(D,RP,Real(MV)).main(w,x) : res ] - 
        Pr [ ZKGame(D,RP,Ideal(S,MV)).main(w,x) : res ] | <= eps,
  for any error *eps*.
*)
require import DBool.

from DVNIZK require import ADVNIZKPProtocol.

theory ZeroKnowledge.

  (** Cloning an abstract DVNIZK protocol. When instantiating zero-knowledge, a concrete protocol
      must be provided. *)
  clone import DVNIZKPProtocol.

  (** Type of randomness generator procedures. Modules that realize this type should contain a 
      **gen** function that takes as input the prover input and generates the prover
      randomness *)
  module type RandP_t = {
    proc gen(xp : prover_input_t) : prover_rand_t
  }.

  (** Distinguisher type. The distinguisher will be given a protocol trace and, knowing the
      witness and the statement, try to distinguish if the trace received came from a protocol
      execution or from a simulator *)
  module type Distinguisher_t = {
    proc guess(_ : witness_t * statement_t * trace_t option) : bool
  }.

  (** Evalutator type. Modules that realize the **Evaluator_t** type must produce a protocol
      trace, given the inputs to the protocol and the appropriate prover randomness *)
  module type Evaluator_t = {
    proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : trace_t option
  }.

  (** Zero-knowledge cryptographic experience *)
  module ZKGame (D : Distinguisher_t) (RP : RandP_t) (E : Evaluator_t) = {
    proc main(w : witness_t, x : statement_t) : bool = {
      var ctr, rp, b';

      rp <@ RP.gen(w,x);
      if (DVNIZKPProtocol.valid_rand_prover rp (w,x)) {
        ctr <@ E.eval(w,x,rp);
        b' <@ D.guess(w,x,ctr);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  (** Malicious verifier type. A malicious verifier is able to produce a decision given the
      statement and the commitment from the prover *)
  module type MVerifier_t = {
    proc prove(x : statement_t, c : commitment_t) : bool
  }.

  (** Real evaluator module. In this module, an execution of the protocol with a dishonest
      verifier takes plance *)
  module RealEvaluator (MV : MVerifier_t) = {
    proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : trace_t option = {
      var c, b, r;

      c <- commit rp (w,x);
      b <@ MV.prove(x, c);
      r <- Some c;

      return r;
    }
  }.

  (** Simulator type. A simulator should be able to *simulate* a commitment, given only the 
      prover randomness and the statement (i.e., without knowing the witness) *)
  module type Simulator_t = {
    proc gen_commitment(rp : prover_rand_t, x : statement_t) : commitment_t option
  }.

  (** Ideal evaluator module. In this module, the dishonest verifier interacts with a simulator
      instead of with a real prover party *)
  module IdealEvaluator (MV : MVerifier_t) (S : Simulator_t) = {
    proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : trace_t option = {
      var c, b, ret, oc;

      ret <- None;
      oc <@ S.gen_commitment(rp, x);
      if (oc <> None) {
        c <- oget oc;
        b <@ MV.prove(x, c);
        ret <- Some c;
      }

      return ret;
    }
  }.

  (** *Real* world game of the zero-knowledge definition. The *real* world instantiates the 
      **ZKGame** with the real evaluator *)
  module GameReal (D : Distinguisher_t) (RP : RandP_t) (MV : MVerifier_t) = ZKGame(D,RP,RealEvaluator(MV)).
  (** *Ideal* world game of the zero-knowledge definition. The *ideal* world instantiates the 
      **ZKGame** with the ideal evaluator and with a simulator **S** *)
  module GameIdeal (D : Distinguisher_t) (RP : RandP_t) (MV : MVerifier_t) (S : Simulator_t) = ZKGame(D,RP,IdealEvaluator(MV,S)).

end ZeroKnowledge.
