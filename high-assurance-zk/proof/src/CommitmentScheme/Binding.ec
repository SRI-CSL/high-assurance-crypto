from CommitmentScheme require import ACommitmentScheme.

theory Binding.

  clone import CommitmentScheme.

  type aux_t.

  module type Adversary_t = {
    proc choose(_ : aux_t) : commitment_t * msg_t * opening_string_t * msg_t * opening_string_t
  }.

  module Game(A : Adversary_t) = {

    proc main(aux : aux_t) : bool = {
      var c, m0, ok0, m1, ok1, b0, b1, ret;

      ret <- false;
      (c,m0,ok0,m1,ok1) <@ A.choose(aux);
      b0 <- verify m0 (c, ok0);
      b1 <- verify m1 (c, ok1);

      return b0 /\ b1 /\ m0 <> m1;
    }
  }.

end Binding.
