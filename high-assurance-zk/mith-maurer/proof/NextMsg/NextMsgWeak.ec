require import AllCore Int List Distr.
require import Aux AuxList NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol.
require import NextMsgISet NextMsgIMap.

theory Weak.

  clone import StatefulProtocol as P.
  import P.

  type secret_input.
  type public_output.
  type rand = ST.local_rand ST.pmap.
  type local_inputs = ST.local_input ST.pmap.
  type local_outputs = ST.local_output ST.pmap.
  type public_input = ST.public_input.

  op unshare_input : local_inputs -> secret_input.
  op unshare_output : local_outputs -> public_output. 

  op functionality : public_input -> secret_input -> public_output.

  type 'a cmap = 'a IMap.imap.
  type corrupted_parties = ISet.iset.
  op corrupted_t : int.

  axiom corrupted_le : corrupted_t <= P.ST.parties.
  type corrupted_inputs = ST.local_input cmap.
  type corrupted_outputs = ST.local_output cmap.
  type corrupted_views = ST.view cmap.

  op corrupted_set (i:ISet.iset) : bool = ISet.card i = corrupted_t /\ ISet.subset i P.ST.partyset.
  op corrupted (i:ISet.iset) (xs:'a ST.P.arrayN) : 'a cmap =
    IMap.ofset (fun i => ST.P.get xs i) i.
  abbrev corrupted2 i : ('a ST.P.arrayN * 'b ST.P.arrayN) -> ('a cmap * 'b cmap) =
    (prod (corrupted i) (corrupted i)).
  abbrev corrupted3 i (xyz:('a ST.P.arrayN * ('b ST.P.arrayN * 'c ST.P.arrayN))) : ('a cmap * ('b cmap * 'c cmap)) =
    (corrupted i xyz.`1,(corrupted i xyz.`2.`1,corrupted i xyz.`2.`2)).

  op corrupted_view_outputs (cr:ISet.iset) (x:public_input) (vs:ST.view cmap) : ST.local_output cmap =
    IMap.ofset (fun i => view_output i x (oget (IMap.get vs i) )) cr.

  op simulator : corrupted_parties -> public_input -> corrupted_inputs -> rand -> corrupted_views.
  op simulator_out (i:corrupted_parties) (x:public_input) (yi:corrupted_inputs) (cs:rand) :  corrupted_views * corrupted_outputs =
    let vi = simulator i x yi cs in
    let zi = corrupted_view_outputs i x vi in
    (vi,zi).

  op gen_rand : public_input -> rand distr.

end Weak.
