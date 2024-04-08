require import Distr Real.

from SigmaProtocol require import ASigmaProtocol.

theory Soundness.

  clone import SigmaProtocol.

  module type MProver_t = {
    proc commitment(x : statement_t) : commit_t
    proc response(ch : challenge_t) : response_t
  }.

  module type RandV_t = {
    proc gen() : verifier_rand_t
  }.
  
  module Soundness(RV : RandV_t, MP : MProver_t) = {
    proc main(x : statement_t) : bool = {
      var r_v, b, c, ch, resp, stv;

      r_v <@ RV.gen();
      if (valid_rand_verifier r_v x) {
        c <@ MP.commitment(x);
        if (valid_commit c) {
          (stv,ch) <- challenge r_v x c;
          resp <@ MP.response(ch);
          b <- !language x /\ decide stv resp;
        } else { b <- false; }
      } else { b <- false; }

      return b;
    }
  }.
  
end Soundness.
