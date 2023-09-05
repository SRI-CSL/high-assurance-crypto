require import AllCore Int List Distr.
require import Aux AuxList NextMsgISet NextMsgIMap.
require import NextMsgArray NextMsgFixedArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit NextMsgWeak.

theory WeakGate.

  clone import Gate as G.

  type secret.
  op unshare : share G.GT.pmap -> secret.

  clone include Weak with
    theory P = G,
    type secret_input = secret,
    type public_output = secret,
    op unshare_input = unshare,
    op unshare_output = unshare.

  (*lemma gate_valid_randsE x cs :
    P.valid_rands x cs = gate_valid_rands x cs.
    rewrite /P.valid_rands /gate_valid_rands G.GT.P.allP => />. rewrite eq_logical => />. progress. have : (G.consistent_rands x i i ((GT.P.get cs i)) ((GT.P.get cs i))). rewrite H => />. rewrite !ISet.iset_in_def => />. rewrite /consistent_rands => />H2. rewrite /valid_rands => />i j Hi Hj.
    rewrite H => />*. move :Hi. rewrite !ISet.iset_in_def => />*.
    rewrite H => />*. move :Hj. rewrite !ISet.iset_in_def => />*. qed.*)

end WeakGate.

theory WeakCircuit.

  clone import WeakGate as WG.

  clone import Circuit as B with
    theory G = WG.G.

  op circ_gen_rand' (c:WG.G.Gate list) : ((WG.G.GT.local_rand list) B.CT.pmap) distr =
    dapply CT.P.concat (djoin (map (WG.gen_rand) c)).

  op circ_gen_rand (c:Circuit) : (B.CT.local_rand B.CT.pmap) distr =
    (circ_gen_rand' c).

  op circ_functionality (c:Circuit) (ws:WG.secret) : WG.secret =
    foldl (transpose WG.functionality) ws c.

  op circ_simulator' (i:ISet.iset) (c:WG.G.Gate list) (wis: B.CT.local_input WG.cmap) (cs:(WG.G.GT.local_rand list) B.CT.pmap) : ((B.CT.msg list) B.CT.pmap) WG.cmap * ((WG.G.GT.local_rand list) WG.cmap * B.CT.local_output WG.cmap) =
    with c = [] =>
      let ins = IMap.ofset (fun _ => B.CT.pinit (fun _ => [])) i in
      let rs = IMap.ofset (fun _ => []) i in
      (ins,(rs,IMap.redom i wis))
    with c = g :: c' =>
      let vp = WG.simulator_out i g wis (B.CT.P.map (head witness) cs) in
      let wis' = vp.`2 in
      let vsp = circ_simulator' i c' wis' (B.CT.P.map behead cs) in
      let ins = IMap.map (fun (v:WG.G.GT.view) => B.CT.P.map (fun rs => Array.get rs 0) v.`2.`1) vp.`1 in
      let ins' = IMap.merge B.CT.pcons ins vsp.`1 in
      let rs' = IMap.merge cons (IMap.map thr3 vp.`1) vsp.`2.`1 in
      (ins',(rs',vsp.`2.`2)).

  op circ_simulator_sz sz (i:ISet.iset) (c:Circuit) (wis: B.CT.local_input WG.cmap) (cs:B.CT.local_rand B.CT.pmap) : B.CT.view WG.cmap =
    let o = circ_simulator' i c wis cs in
    let vins = IMap.map (B.CT.P.map (B.CT.rlist sz)) o.`1 in
    let vcs = o.`2.`1 in
    IMap.redom i (IMap.zip wis (IMap.zip vins vcs)).

  op circ_simulator (i:ISet.iset) (c:Circuit) (wis: B.CT.local_input WG.cmap) (cs:B.CT.local_rand B.CT.pmap) : B.CT.view WG.cmap =
      circ_simulator_sz (List.size c) i c wis cs.

  clone include Weak with
    theory P = B,

    op corrupted_t = WG.corrupted_t,
    type secret_input = WG.secret,
    type public_output = WG.secret,
    op unshare_input = WG.unshare,
    op unshare_output = WG.unshare,
    op gen_rand x = circ_gen_rand x,
    op functionality = circ_functionality,
    op simulator = circ_simulator.

end WeakCircuit.
