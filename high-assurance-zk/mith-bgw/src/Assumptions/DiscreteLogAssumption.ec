from General require import PrimeField CyclicGroup.

theory DiscreteLogarithm.

  module type Adversary_t = {
    proc guess(h : group) : t option
  }.

  module Game(A:Adversary_t) = {
    proc main (h : group) : bool = {
      var x;

      x <@ A.guess(h);

      return (x = Some (log h));
    }
  }.

end DiscreteLogarithm.
