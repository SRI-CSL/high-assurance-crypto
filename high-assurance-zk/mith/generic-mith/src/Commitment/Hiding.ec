require import DBool.

from Commitment require import ACommitmentScheme.

theory Hiding.

  clone import CommitmentScheme.
  
  type aux_t.

  module type Rand_t = {
    proc gen(_ : aux_t) : rand_t
  }.

  module type Adversary_t = {
    proc choose(_ : aux_t) : msg_t * msg_t * aux_t
    proc guess(c : commitment_t) : bool
  }.

  op valid_query : msg_t * msg_t * aux_t -> bool.

  module Game(R : Rand_t, A : Adversary_t) = {

    proc game(aux : aux_t, b : bool) : bool = {
      var r, c, ok, m0, m1, b';

      (m0,m1,aux) <@ A.choose(aux);
      r <@ R.gen(aux);
      if (valid_query (m0,m1,aux) /\ valid_rand r) {
        (c, ok) <- commit r (b ? m1 : m0);
        b' <@ A.guess(c);
      } else { b' <${0,1}; }

      return (b = b');
    }

    proc main(aux : aux_t) : bool = {
      var b, adv;
      b <$ {0,1};
      adv <@ game(aux,b);
      return (adv);
    }
  }.

end Hiding.
