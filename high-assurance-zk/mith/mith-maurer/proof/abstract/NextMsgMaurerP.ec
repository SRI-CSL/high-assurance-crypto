require import AllCore Int List Distr Ring.
require import Aux AuxList.
require import NextMsgFixedArray.

theory MaurerP.

  clone include ArrayN with
    type 'a arrayN = 'a array5,
    op size = 5,
    op get ['a] = nth_array5,
    op set ['a] = set_array5,
    op init ['a] = init_array5
    proof *.
    realize size_ge0.
    rewrite /size => |>*. qed.
    realize get_out.
    rewrite /get /size => />t i H.
    rewrite /nth_array5 => />. smt(). qed.
    realize get_set_eqE.
    rewrite /size /get /set => />m x b Hx1 Hx2.
    rewrite /nth_array5 /set_array5 => />.
    case (x=0) => />H0. case (x=1) => />H1. case (x=2) => />H2. case (x=3) => />H3. case (x=4) => />H4. have : false. smt(). progress. qed.
    realize get_set_neqE.
    rewrite /size /get /set => />m x b a H.
    rewrite /nth_array5 /set_array5 => />.
    case (x=0) => />. rewrite H => />. 
    case (x=1) => />. rewrite H => />.
    case (x=2) => />. rewrite H => />.
    case (x=3) => />. rewrite H => />.
    case (x=4) => />. rewrite H => />.
    case (b=0) => />.
    case (b=1) => />. rewrite /set_array4 /set_array3 /set_array2 => />. smt().
    case (b=2) => />. rewrite /set_array4 /set_array3 /set_array2 => />. smt().
    case (b=3) => />. rewrite /set_array4 /set_array3 /set_array2 => />. smt().
    case (b=4) => />. rewrite /set_array4 /set_array3 /set_array2 => />. smt().
    qed.
    realize get_init.
    rewrite /get /init /size /nth_array5 /init_array5 /array5 => />f i. smt(). qed.
    realize tP.
    rewrite /size /get => />t1 t2 H.
    have : nth_array5 t1 0 = nth_array5 t2 0. rewrite H => />.
    have : nth_array5 t1 1 = nth_array5 t2 1. rewrite H => />.
    have : nth_array5 t1 2 = nth_array5 t2 2. rewrite H => />.
    have : nth_array5 t1 3 = nth_array5 t2 3. rewrite H => />.
    have : nth_array5 t1 4 = nth_array5 t2 4. rewrite H => />.
    rewrite /nth_array5 !eq2 => />. qed.

end MaurerP.
