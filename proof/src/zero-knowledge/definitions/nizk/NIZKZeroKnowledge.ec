require import DBool.

from NIZK require import ANIZKProtocol.

theory ZeroKnowledge.

  clone import NIZKProtocol.

  module type RandP_t = {
    proc gen(xp : prover_input_t) : prover_rand_t
  }.

  module type Distinguisher_t = {
    proc init() : prover_input_t * verifier_input_t
    proc guess(_ : trace_t option) : bool
  }.

  module type Evaluator_t = {
    proc init(x  : prover_input_t * verifier_input_t) : unit
    proc eval() : trace_t option
  }.

  module type MVerifier_t = {
    proc prove(x : statement_t, c : commitment_t) : bool
  }.

  module RealEvaluator (R : RandP_t) (MV : MVerifier_t) = {
    var xp : prover_input_t

    proc init (x : prover_input_t * verifier_input_t) = {
      xp <- fst x;
    }

    proc eval() : trace_t option = {
      var c, b, r, rp;

      r <- None;
      rp <@ R.gen(xp);
      if (valid_rand_prover rp xp) {
        c <- commit rp xp;
        b <@ MV.prove(xp.`2, c);
        r <- Some (c);
      }
      return r;
    }
  }.

  module ZKGame (D : Distinguisher_t) (E : Evaluator_t) = {
    proc main() : bool = {
      var b', xp, xv, v;

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

  (** Simulator type. A simulator should be able to *simulate* a commitment, given only the 
      prover randomness and the statement (i.e., without knowing the witness) *)
  module type Simulator_t = {
    proc init() : verifier_input_t
    proc gen_commitment(x : statement_t) : commitment_t option
  }.

  (** Ideal evaluator module. In this module, the dishonest verifier interacts with a simulator
      instead of with a real prover party *)
  module IdealEvaluator (MV : MVerifier_t) (S : Simulator_t) = {
    var yv : verifier_output_t
    var statement : statement_t

    proc init(x : prover_input_t * verifier_input_t) = {
      var xv;
      
      xv <@ S.init();
      yv <- relation x.`1.`1 xv;
      statement <- xv;
    } 

    proc eval() : trace_t option = {
      var c, b, ret, oc;

      ret <- None;
      oc <@ S.gen_commitment(statement);
      if (oc <> None) {
        c <- oget oc;
        b <@ MV.prove(statement, c);
        ret <- Some (c);
      }

      return ret;
    }
  }.

  (** *Real* world game of the zero-knowledge definition. The *real* world instantiates the 
      **ZKGame** with the real evaluator *)
  module GameReal (D : Distinguisher_t) (RP : RandP_t) (MV : MVerifier_t) = ZKGame(D,RealEvaluator(RP, MV)).
  (** *Ideal* world game of the zero-knowledge definition. The *ideal* world instantiates the 
      **ZKGame** with the ideal evaluator and with a simulator **S** *)
  module GameIdeal (D : Distinguisher_t) (MV : MVerifier_t) (S : Simulator_t) = ZKGame(D,IdealEvaluator(MV,S)).

end ZeroKnowledge.
