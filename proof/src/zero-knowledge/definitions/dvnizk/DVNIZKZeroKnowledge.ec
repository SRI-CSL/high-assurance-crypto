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

from DVNIZK require import ADVNIZKProtocol.

theory ZeroKnowledge.

  (** Cloning an abstract DVNIZK protocol. When instantiating zero-knowledge, a concrete protocol
      must be provided. *)
  clone import DVNIZKProtocol.

  (** Type of randomness generator procedures. Modules that realize this type should contain a 
      **gen** function that takes as input the prover input and generates the prover
      randomness *)
  module type RandP_t = {
    proc gen(xp : statement_t) : prover_rand_t
  }.

  (** Distinguisher type. The distinguisher will be given a protocol trace and, knowing the
      witness and the statement, try to distinguish if the trace received came from a protocol
      execution or from a simulator *)
  module type Distinguisher_t = {
    proc init() : prover_input_t * verifier_input_t
    proc guess(_ : trace_t option) : bool
  }.

  (** Malicious verifier type. A malicious verifier is able to produce a decision given the
      statement and the commitment from the prover *)
  module type MVerifier_t = {
    proc prove(x : statement_t, c : commitment_t) : bool
  }.

  (** Evalutator type. Modules that realize the **Evaluator_t** type must produce a protocol
      trace, given the inputs to the protocol and the appropriate prover randomness *)
  module type Evaluator_t = {
    proc init(x : prover_input_t * verifier_input_t) : unit
    proc eval() : trace_t option
  }.

  (** Simulator type. A simulator should be able to *simulate* a commitment, given only the 
      prover randomness and the statement (i.e., without knowing the witness) *)
  module type Simulator_t = {
    proc init(x : statement_t) : unit
    proc gen_commitment() : commitment_t option
  }.

  (** Real evaluator module. In this module, an execution of the protocol with a dishonest
      verifier takes plance *)
  module RealEvaluator (RP : RandP_t) (MV : MVerifier_t) = {
    var xp : prover_input_t

    proc init(x : prover_input_t * verifier_input_t) : unit = {
      xp <- x.`1;
    }
    proc eval() : trace_t option = {
      var c, b, r, rp;

      r <- None;
      rp <@ RP.gen(xp.`2);
      if (valid_rand_prover rp xp.`2) {
        c <- commit rp xp;
        b <@ MV.prove(xp.`2, c);
        r <- Some c;
      }
      return r;
    }
  }.

  (** Ideal evaluator module. In this module, the dishonest verifier interacts with a simulator
      instead of with a real prover party *)
  module IdealEvaluator (MV : MVerifier_t) (S : Simulator_t) = {
    var yv : verifier_output_t
    var statement : statement_t
    var xp : prover_input_t

    proc init(x : prover_input_t * verifier_input_t) : unit = {
      S.init(x.`2);
      yv <- relation x.`1.`1 x.`2;
      statement <- x.`2;
      xp <- x.`1;
    }

    proc eval() : trace_t option = {
      var c, b, ret, oc;

      ret <- None;
        oc <@ S.gen_commitment();
        if (oc <> None) {
          c <- oget oc;
          b <@ MV.prove(statement, c);
          ret <- Some c;
        }
      return ret;
    }
  }.

  (** Zero-knowledge cryptographic experience *)
  module ZKGame (D : Distinguisher_t) (E : Evaluator_t) = {
    proc main() : bool = {
      var xp, xv, v, b';

      (xp, xv) <@ D.init();
      v <- None;
      if (valid_inputs (xp, xv)) {
        E.init(xp, xv);
        v <@ E.eval();
      }

      b' <@ D.guess(v);

      return b';
    }
  }.

  (** *Real* world game of the zero-knowledge definition. The *real* world instantiates the 
      **ZKGame** with the real evaluator *)
  module GameReal (D : Distinguisher_t) (RP : RandP_t) (MV : MVerifier_t) = ZKGame(D,RealEvaluator(RP, MV)).
  (** *Ideal* world game of the zero-knowledge definition. The *ideal* world instantiates the 
      **ZKGame** with the ideal evaluator and with a simulator **S** *)
  module GameIdeal (D : Distinguisher_t) (MV : MVerifier_t) (S : Simulator_t) = ZKGame(D,IdealEvaluator(MV,S)).

end ZeroKnowledge.
