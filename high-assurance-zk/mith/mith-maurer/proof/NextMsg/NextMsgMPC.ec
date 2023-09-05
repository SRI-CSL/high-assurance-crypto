require import AllCore Int List Distr.
require import Aux NextMsgIMap NextMsgISet NextMsgArray NextMsgFixedArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgWeak.

theory MPC.

  clone import StatefulProtocol as P.
  
  type rand = ST.local_rand ST.pmap.
  type local_inputs = ST.local_input ST.pmap.
  type local_outputs = ST.local_output ST.pmap.
  type public_input = ST.public_input.
  type public_output = ST.local_output.

  op functionality : public_input -> local_inputs -> public_output.

  type corrupted_parties = ISet.iset.
  op corrupted_t : int.

  type 'a cmap = 'a IMap.imap.
  axiom corrupted_le : corrupted_t <= P.ST.parties.
  type corrupted_inputs = ST.local_input cmap.
  type corrupted_outputs = ST.local_output cmap.
  type corrupted_views = ST.view cmap.

  op corrupted_set (i:ISet.iset) : bool = ISet.card i = corrupted_t /\ ISet.subset i P.ST.partyset.
  op corrupted (cr:ISet.iset) (xs:'a ST.P.arrayN) : 'a cmap =
    IMap.ofset (fun i => ST.P.get xs i) cr.
  abbrev corrupted2 cr : ('a ST.P.arrayN * 'b ST.P.arrayN) -> ('a cmap * 'b cmap) =
    prod (corrupted cr) (corrupted cr).
  abbrev corrupted3 cr (xyz:('a ST.P.arrayN * ('b ST.P.arrayN * 'c ST.P.arrayN))) : ('a cmap * ('b cmap * 'c cmap)) =
    (corrupted cr xyz.`1,(corrupted cr xyz.`2.`1,corrupted cr xyz.`2.`2)).

  op corrupted_view_outputs (cr:ISet.iset) (x:public_input) (vs:ST.view cmap) : ST.local_output cmap =
    IMap.ofset (fun i => view_output i x (oget (IMap.get vs i)) ) cr.

  op simulator : corrupted_parties -> public_input -> corrupted_inputs -> rand -> public_output -> corrupted_views.

  op gen_rand : public_input -> rand distr.

end MPC.
