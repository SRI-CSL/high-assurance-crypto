require import DBool.

from NIZK require import ANIZKProtocol.

theory ZeroKnowledge.

  clone import NIZKProtocol.

  module type RandP_t = {
    proc gen(xp : prover_input_t) : prover_rand_t
  }.

  module type Distinguisher_t = {
    proc guess(_ : witness_t * statement_t * trace_t option) : bool
  }.

  module type Evaluator_t = {
    proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : trace_t option
  }.

  module ZKGame (D : Distinguisher_t) (RP : RandP_t) (E : Evaluator_t) = {
    proc main(w : witness_t, x : statement_t) : bool = {
      var ctr, rp, b';

      rp <@ RP.gen(w,x);
      if (valid_rand_prover rp (w,x)) {
        ctr <@ E.eval(w,x,rp);
        b' <@ D.guess(w,x,ctr);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  module type MVerifier_t = {
    proc prove(x : statement_t, c : commitment_t) : bool
  }.

  module RealEvaluator (MV : MVerifier_t) = {
    proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : trace_t option = {
      var c, b, r;

      c <- commit rp (w,x);
      b <@ MV.prove(x, c);
      r <- Some c;

      return r;
    }
  }.

  module type Simulator_t = {
    proc gen_commitment(rp : prover_rand_t, x : statement_t) : commitment_t option
  }.

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

  module GameReal (D : Distinguisher_t) (RP : RandP_t) (MV : MVerifier_t) = ZKGame(D,RP,RealEvaluator(MV)).
  module GameIdeal (D : Distinguisher_t) (RP : RandP_t) (MV : MVerifier_t) (S : Simulator_t) = ZKGame(D,RP,IdealEvaluator(MV,S)).

end ZeroKnowledge.
