require import AllCore Int List Distr.
require import Aux AuxList NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol.
require import FSet SmtMap AuxFSet AuxSmtMap NextMsgISet NextMsgIMap.
require import NextMsgWeak.

theory WeakProofs.

  clone import Weak as W.

  axiom gen_rand_ll p :
    is_lossless (gen_rand p).

  axiom valid_gen_rand x rs :
    rs \in gen_rand x => P.valid_rands x rs.

  axiom weak_correctness (x:public_input) (ys:local_inputs) (cs:rand):
    P.valid_inputs x ys /\ P.valid_rands x cs => 
      functionality x (unshare_input ys) = unshare_output (W.P.protocol x ys cs).`2.

  module WeakPrivacy = {
    proc ideal(i,p,ys) = {
      var cs,yi;
      yi <- corrupted i ys;
      cs <$ gen_rand p;
      return simulator i p yi cs;
    }
    proc ideal_out(i,p,ys) = {
      var cs,yi;
      yi <- corrupted i ys;
      cs <$ gen_rand p;
      return simulator_out i p yi cs;
    }
    proc ideal_out'(i,p,yi) = {
      var cs;
      cs <$ gen_rand p;
      return simulator_out i p yi cs;
    }
    proc real(i,p,ys) = {
      var cs;
      cs <$ gen_rand p;
      return corrupted i (W.P.protocol p ys cs).`1;
    }
    proc real_out(i,p,ys) = {
      var cs,tro;
      cs <$ gen_rand p;
      tro <- W.P.protocol p ys cs;
      return (corrupted2 i tro);
    }
    proc real_out'(p,ys) = {
      var cs;
      cs <$ gen_rand p;
      return W.P.protocol p ys cs;
    }
  }.
  axiom dom_simulator i x ws r :
    fdom (simulator i x ws r) = i.
  lemma dom_simulator_out i x ws r :
    fdom (simulator_out i x ws r).`1 = i.
  rewrite /simulator_out => />*. rewrite dom_simulator => />*. qed.
  lemma dom_corrupted i (xs:'a W.P.ST.P.arrayN) :
    fdom (corrupted i xs) = i.
    rewrite /corrupted /IMap.ofset fdom_ofset => />*. qed.

  axiom weak_privacy :
    equiv [WeakPrivacy.ideal ~ WeakPrivacy.real : ={i,p,ys} /\ corrupted_set i{1} /\ P.valid_inputs p{1} ys{1} ==> ={res} ].

  lemma get_corrupted (xs:'a P.ST.pmap) (i:P.ST.party) (cr:ISet.iset) :
    ISet.mem i cr /\ corrupted_set cr => oget (IMap.get (corrupted cr xs) i) = P.ST.P.get xs i.
    rewrite /corrupted /ISet.mem => />H1 H2 H3. rewrite /IMap.get /IMap.ofset get_ofset => />*. rewrite H1 => />*. qed.

  lemma view_outputs_corrupted i x xs :
    corrupted_set i => 
      corrupted_view_outputs i x (corrupted i xs) = corrupted i (W.P.view_outputs x xs).
    rewrite /view_outputs /corrupted_view_outputs /corrupted /corrupted_set => />H1 H2. rewrite /IMap.ofset -fmap_eqIn => />*. rewrite !fdom_ofset => />y Hy. rewrite !get_ofset !Hy => />. rewrite P.ST.get_pimap => />*. rewrite /ISet.mem (in_subset i) => />. rewrite /IMap.get /IMap.ofset !get_ofset !Hy => />. qed.
       
  lemma weak_privacy_out :
    equiv [WeakPrivacy.ideal_out ~ WeakPrivacy.real_out : ={i,p,ys} /\ corrupted_set i{1} /\ P.valid_inputs p{1} ys{1} ==> ={res} ].
    proc. inline WeakPrivacy.ideal_out WeakPrivacy.real_out. sp. 
    alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 vi = simulator i p yi cs.
    alias{2} 1 t = 0. swap{2} 1 1. alias{2} 2 vi = corrupted i (W.P.protocol p ys cs).`1.
    transitivity{1}
      { vi <@ WeakPrivacy.ideal(i,p,ys); }
      (={i,p,ys} /\ yi{1} = corrupted i{1} ys{1} ==> ={i,p,ys,vi} /\ yi{1} = corrupted i{1} ys{1} /\ vi{2} = simulator i{1} p{1} yi{1} cs{1})
      (={i,p,ys} /\ yi{1} = corrupted i{1} ys{1} /\ corrupted_set i{2} /\ P.valid_inputs p{2} ys{2} ==> ={i,p,ys,vi} /\ corrupted_set i{2} /\ vi{1} = corrupted i{2} (W.P.protocol p{2} ys{2} cs{2}).`1 /\ P.valid_inputs p{2} ys{2} /\ P.valid_rands p{2} cs{2} /\ tro{2} = W.P.protocol p{2} ys{2} cs{2} ).
      progress. exists (i{2}) (p{2}) (corrupted i{2} ys{2}) (ys{2}) => />*.
      rewrite /simulator_out. progress. rewrite H0. rewrite view_outputs_corrupted => />*. rewrite W.P.protocol_consistency => />*. 
    inline *. wp. sp. auto => />*. 
    transitivity{1}
      { vi <@ WeakPrivacy.real(i,p,ys); }
      (={i,p,ys} /\ corrupted_set i{2} /\ P.valid_inputs p{1} ys{1} ==> ={i,p,ys,vi})
      (={i,p,ys} /\ corrupted_set i{2} /\ P.valid_inputs p{2} ys{2} ==> ={i,p,ys,vi} /\ corrupted_set i{2} /\ P.valid_inputs p{2} ys{2} /\ P.valid_rands p{2} cs{2} /\ tro{2} = W.P.protocol p{2} ys{2} cs{2} /\ vi{1} = corrupted i{2} (W.P.protocol p{2} ys{2} cs{2}).`1).
      progress. exists (i{2}) (p{2}) (ys{2}) => />*. auto => />*.
    call (weak_privacy). auto => />*.
    inline *. wp. sp. auto. progress. have : P.valid_rands p{2} cs0L. rewrite (valid_gen_rand p{2}) => />*. progress. 
    qed.

  lemma weak_privacy_out' I : 
    equiv [WeakPrivacy.ideal_out' ~ WeakPrivacy.real_out' : corrupted_set i{1} /\ P.valid_inputs p{2} ys{2} /\ I=i{1} /\ ={p} /\  yi{1} = corrupted I ys{2} ==> res{1} = corrupted2 I res{2} ].
    proc. simplify.
    alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 sivi = simulator_out I p yi cs.
    alias{2} 1 t = 0. swap{2} 1 1. alias{2} 2 sivi = corrupted2 I (P.protocol p ys cs).
    transitivity{2}
      { sivi <@ WeakPrivacy.real_out(I,p,ys); }
      (={p} /\ corrupted_set i{1} /\ P.valid_inputs p{2} ys{2} /\ yi{1} = corrupted I ys{2} /\ i{1}=I ==> i{1}=I /\ P.valid_inputs p{2} ys{2} /\ corrupted_set i{1} /\ ={sivi} /\ sivi{1} = simulator_out I p{1} yi{1} cs{1} )
      (={p,ys} /\ P.valid_inputs p{2} ys{2} ==> ={p,ys,sivi} /\ sivi{2} = corrupted2 I (P.protocol p{2} ys{2} cs{2}) /\ P.valid_inputs p{2} ys{2} ).
      progress. exists (p{2}) (ys{2}). progress. progress.
    transitivity{2}
      { sivi <@ WeakPrivacy.ideal_out(I,p,ys); }
       (={p} /\ corrupted_set i{1} /\ P.valid_inputs p{2} ys{2} /\ yi{1} = corrupted I ys{2} /\ i{1}=I ==> corrupted_set i{1} /\ P.valid_inputs p{2} ys{2} /\ i{1}=I /\ ={sivi} /\ sivi{1} = simulator_out I p{1} yi{1} cs{1})
      (={p,ys} /\ corrupted_set I /\ P.valid_inputs p{2} ys{2} ==> ={p,ys,sivi} ).
      progress. exists (p{2}) (ys{2}). progress. progress.
    inline *. wp. sp. auto => />*.
    call weak_privacy_out => />*. progress.
    inline *. wp. sp. auto => />*.
    qed.

end WeakProofs.

