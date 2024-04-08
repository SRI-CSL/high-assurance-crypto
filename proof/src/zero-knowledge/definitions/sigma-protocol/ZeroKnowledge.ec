require import DBool.

from SigmaProtocol require import ASigmaProtocol.

theory ZeroKnowledge.

  clone import SigmaProtocol.

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
      if (SigmaProtocol.valid_rand_prover rp (w,x)) {
        ctr <@ E.eval(w,x,rp);
        b' <@ D.guess(w, x, ctr);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  module type MVerifier_t = {
    proc challenge(x : statement_t, c : commit_t) : challenge_t
  }.

  module RealEvaluator (MV : MVerifier_t) = {
    proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : trace_t option = {
      var c, ch, resp, stp, r, y1;

      (stp,c) <- commit rp (w,x);
      r <- None;
      if (valid_commit c) {
        ch <@ MV.challenge(x, c);
        if (valid_challenge ch) {
          (y1, resp) <- response stp ch;
          if (valid_response resp) {
            r <- Some (c,ch,resp);
          }
        }
      }

      return r;
    }
  }.

  module type Simulator_t = {
    proc commit(rp : prover_rand_t, x : statement_t) : commit_t
    proc response(x : statement_t, ch : challenge_t) : response_t
  }.

  module IdealEvaluator (MV : MVerifier_t) (S : Simulator_t) = {
    proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : trace_t option = {
      var c, ch, resp, ret;

      ret <- None;
      c <@ S.commit(rp, x);
      if (valid_commit c) {
        ch <@ MV.challenge(x, c);
        if (valid_challenge ch) {
          resp <@ S.response(x, ch);
          if (valid_response resp) {
            ret <- Some (c,ch, resp);
          }
        }
      }

      return ret;
    }
  }.

  module GameReal (D : Distinguisher_t) (RP : RandP_t) (MV : MVerifier_t) = ZKGame(D,RP,RealEvaluator(MV)).
  module GameIdeal (D : Distinguisher_t) (RP : RandP_t) (MV : MVerifier_t) (S : Simulator_t) = ZKGame(D,RP,IdealEvaluator(MV,S)).

end ZeroKnowledge.
