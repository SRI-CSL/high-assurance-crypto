from NIZK require import ANIZKProtocol.

theory Soundness.

  clone import NIZKProtocol.

  module type MProver_t = {
    proc commit(x : statement_t) : commitment_t
  }.

  module type RandV_t = {
    proc gen() : verifier_rand_t
  }.
  
  module Soundness(R : RandV_t, MP : MProver_t) = {
    proc main(rp : prover_rand_t, x : statement_t) : bool = {
      var b, c, rv;

      c <@ MP.commit(x);

      rv <@ R.gen();
      if (valid_rand_verifier rv x) {
        b <- !language x /\ prove rv x c;
      } else { b <- false; }

      return b;
    }
  }.
  
end Soundness.
