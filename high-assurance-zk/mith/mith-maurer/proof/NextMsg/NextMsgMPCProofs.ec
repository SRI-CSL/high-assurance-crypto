require import AllCore Int List Distr.
require import Aux FSet SmtMap AuxFSet AuxSmtMap NextMsgIMap NextMsgISet NextMsgArray NextMsgFixedArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgWeak NextMsgMPC NextMsgWeakProofs.

theory MPCProofs.

  clone import MPC as M.

  axiom gen_rand_ll p :
    is_lossless (gen_rand p).

  axiom valid_gen_rand x rs :
    rs \in gen_rand x => P.valid_rands x rs.

  axiom mpc_correctness (x:public_input) (ys:local_inputs) (cs:rand) :
    P.valid_inputs x ys /\ P.valid_rands x cs =>
      M.P.ST.pinit (fun _ => functionality x ys) = (M.P.stateful_protocol x ys cs).`2.

  axiom dom_simulator i x ws r o :
    fdom (simulator i x ws r o) = i.
  lemma dom_corrupted i (xs:'a M.P.ST.P.arrayN) :
    fdom (corrupted i xs) = i.
    rewrite /corrupted fdom_ofset => />*. qed.

  module MPCPrivacy = {
    proc ideal(i,x,ss) = {
      var cs,y,si,vi;
      y <- functionality x ss;
      si <- corrupted i ss;
      cs <$ gen_rand x;
      vi <- simulator i x si cs y;
      return vi;
    }
    proc real(i,x,ss) = {
      var y,tr,vi,cs;
      cs <$ gen_rand x;
      (tr,y) <- M.P.stateful_protocol x ss cs;
      vi <- corrupted i tr;
      return vi;
    }
  }.
  
  axiom mpc_privacy :
    equiv [MPCPrivacy.ideal ~ MPCPrivacy.real : ={i,x,ss} /\ ISet.subset i{1} P.ST.partyset /\ ISet.card i{1} = corrupted_t /\ P.valid_inputs x{1} ss{1} ==> ={res} ].

end MPCProofs.
