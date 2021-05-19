require import Real.

from General require import PrimeField CyclicGroup.
from CommitmentScheme require import ACommitmentScheme Hiding Binding.
from Assumptions require import DiscreteLogAssumption.

theory Pedersen.

  op h : group.
  lemma log_h : exists x, cgexp g x = h by exists (log h); rewrite gpow_log.

  type msg_t = t.
  op valid_msg (x : msg_t) : bool = true.

  type rand_t = t.
  op valid_rand (r : rand_t) : bool = true.

  type commitment_t = group.
  type opening_string_t = t.
  type commit_info_t = commitment_t * opening_string_t.

  op commit (r : rand_t) (m : msg_t) : commit_info_t = 
    let c = cgmul (cgexp g r) (cgexp h m) in
    (c,r).

  op verify (m : msg_t) (c : commit_info_t) : bool = 
    let (c,ok) = c in
    c = cgmul (cgexp g ok) (cgexp h m).

  clone export CommitmentScheme as Pedersen with
    type msg_t = msg_t,
    type rand_t = rand_t,
    op valid_rand = valid_rand,
    type commitment_t = commitment_t,
    type opening_string_t = opening_string_t,
    op commit = commit,
    op verify = verify
  proof *.
  realize correct by rewrite /verify /commit => /> *. 

  clone import Hiding with theory CommitmentScheme <- Pedersen, type state_t = unit.

  module Rand : Rand_t = {
    proc gen() : rand_t = {
      var r;
      r <$ FDistr.dt;
      return r;
    }
  }.

(*
  section Hiding.
 
    declare module A : Adversary_t.
    axiom A_choose_ll : islossless A.choose.
    axiom A_guess_ll : islossless A.guess.

    module GameFalse(R : Rand_t, A : Adversary_t) = {
      proc main() : bool = {
        var b, b', r, c, m0, m1, d;

        b <$ {0,1};
        r <@ R.gen();
        (m0,m1) <@ A.choose();
        d <$ FDistr.dt;
        c <- cgexp g d;
        b' <@ A.guess(c);

        return (b = b');
      }
    }.

    equiv game_gamefalse_equiv : Game(Rand,A).main ~ GameFalse(Rand,A).main : ={glob A} ==> ={res}.
    proof.
      proc; inline*.
      swap 4-3.
      seq 1 1 : (#pre /\ ={m0,m1}); first by call (_ : true).
      seq 1 1 : (#pre /\ ={b}); first by rnd.
      call (_ : true); wp.
      rnd (fun r => fadd r (fmul (if b{1} then m1{2} else m0{2}) (log h))) 
          (fun r => fsub r (fmul (if b{1} then m1{2} else m0{2}) (log h))).
      wp; rnd{2}; skip => /> *; do split.
        + by move => *; ringeq.
        + move => *; split; first by ringeq.
          move => *; rewrite /commit /=.
          cut ->: h = cgexp g (log h) by rewrite gpow_log.
          by rewrite pow_pow mul_pow gpow_log mulC.
    qed.

    lemma pr_gamefalse &m : Pr[ GameFalse(Rand,A).main() @ &m : res ] = (1%r / 2%r).
    proof.
      byphoare => //.
      proc; inline*.
      swap 1 6; rnd ((=) b').
      conseq (_ : _ ==> true); first by smt(@DBool).
      call A_guess_ll; wp; rnd; call A_choose_ll; wp; rnd; skip => /> *; do split.
        + by rewrite FDistr.dt_ll.
        + by rewrite FDistr.dt_ll.
    qed.

    lemma hiding &m : Pr[ Game(Rand,A).main() @ &m : res ] = (1%r / 2%r).
    proof. by rewrite -(pr_gamefalse &m); byequiv (game_gamefalse_equiv). qed.

  end section Hiding.

  clone import Binding with theory CommitmentScheme <- Pedersen.

  section Biding.
    declare module A : Adversary_t.
    axiom A_choose_ll : islossless A.choose.

    import DiscreteLogarithm.

    module B (A : Binding.Adversary_t) : Adversary_t = {
      proc guess(h : group) : t option = {
        var r, c, m0, ok0, m1, ok1;
        
        (c,m0,ok0,m1,ok1) <@ A.choose();
        if ((c = cgmul (cgexp g ok0) (cgexp h m0)) /\ (c = cgmul (cgexp g ok1) (cgexp h m1)) /\ m0 <> m1) {
          r <- Some (fdiv (fsub ok0 ok1) (fsub m1 m0));
        }
        else { r <- None; }

        return r;
      }
    }.

    lemma div_mul_eq (x y w z a : t) : 
      fsub z w <> fzero =>
      (fdiv (fsub x y) (fsub z w) = a) = ((fsub x y) = fmul a (fsub z w)). 
    proof. by move => *; smt. qed.

    lemma dlog_reduction : 
      equiv [ Binding.Game(A).main ~ Game(B(A)).main : ={glob A} /\ h{2} = h ==> ={res} ].
    proof.
      proc; inline*.
      wp; call (_ : true); wp; skip => /> *; do split.
        + move => *; rewrite /verify /=; rewrite H.
          move : log_h => *; elim H2 => ? <-.
          rewrite !pow_pow !mul_pow -!pow_bij /= (log_gpow x).
          cut ->: (fadd result_R.`3 (fmul x result_R.`2) = fadd result_R.`5 (fmul x result_R.`4)) = 
                  (result_R.`3 = fadd result_R.`5 (fsub (fmul x result_R.`4) (fmul x result_R.`2))).
            by case (fadd result_R.`3 (fmul x result_R.`2) = fadd result_R.`5 (fmul x result_R.`4)) => ?; smt.
          cut ->: (fdiv (fsub result_R.`3 result_R.`5) (fsub result_R.`4 result_R.`2) = x) = 
                  ((fsub result_R.`3 result_R.`5) = fmul x (fsub result_R.`4 result_R.`2)).
            + by rewrite (div_mul_eq result_R.`3 result_R.`5 result_R.`2 result_R.`4 x); first by smt(@PrimeField). 
          rewrite -mulfNl.
          by case (result_R.`3 = fadd result_R.`5 (fsub (fmul x result_R.`4) (fmul x result_R.`2))) => ?; smt.
      by move => *; rewrite /verify /= H.
    qed.

  end section Biding.
*)
end Pedersen.
