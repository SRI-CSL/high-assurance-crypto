require import AllCore Int List FSet SmtMap Distr DProd.
require import Aux AuxList AuxFSet AuxSmtMap.
require import NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit NextMsgWeak NextMsgWeakProofs NextMsgWeakCircuit.
require import NextMsgISet NextMsgIMap NextMsgArray.

import ISet IMap Array.

theory WeakGateProofs.

  clone import WeakGate as WG.

  lemma g_protocol_fst_def x ws cs :
    (WG.G.protocol x ws cs).`1 = (WG.G.g_protocol x ws cs).`1.
    rewrite /protocol /g_protocol => />*.
    (*trace*)
    rewrite (_:G.ST.P.zip3 ws (WG.G.protocol' x ws cs) cs=G.GT.P.zip3 ws (WG.G.protocol' x ws cs) cs). progress. congr. congr. rewrite /protocol' /protocol'' /rounds iseq_1 => />*. rewrite /protocol_round /local_protocol_round => />*.
    rewrite G.ST.ppmap_eqP => />x0 y H H0. rewrite G.ST.get_pmap => />*. rewrite G.ST.get_pprset !H => />*. rewrite /ppswap !G.ST.get_ppinit !H => />*. rewrite !G.ST.get_prset !H0 => />*. rewrite !G.ST.get_pmap => />*. rewrite !G.ST.get_pinit !H0 => />*. rewrite G.GT.get_pimap => />*. rewrite !G.GT.get_pzip3 !H0 => />*. rewrite G.GT.get_pprempty H0 => />*. rewrite Array.tP => />*. rewrite size_set !size_init => />i Hi1 Hi2. rewrite Array.get_init => />*. have : 0 <= i && i < 1. smt(). move => hip. rewrite !hip => />*. case (i=0) => />*. 
    rewrite Array.get_set_eqE => />*. rewrite size_init => />. rewrite /stateful_local_protocol_round /get_local_state /get_local_state' !iseq_nil /init_local_state => />*. rewrite (G.get_send_messages x 1) => />*. rewrite /valid_messages G.ST.P.allP => />j Hj1 Hj2. rewrite G.ST.P.get_imap => />. rewrite !G.ST.P.get_zip !andabP !andaP => />. rewrite /local_gate_start => />. 
    rewrite G.valid_local_gate_start => />. rewrite (G.from_to_local_messages x 1) => />*. rewrite /valid_pmsgs G.ST.P.allP  => />j Hj1 Hj2. rewrite G.ST.P.get_map => />*. rewrite G.ST.P.get_imap => />*. rewrite G.ST.P.get_zip !andabP !andaP => />*.
    have : G.valid_pmsgs x 1 (G.from_local_messages (G.local_gate_start j x (G.GT.P.get ws j) (G.GT.P.get cs j))). rewrite G.valid_pmsgs_from => />. rewrite G.valid_local_gate_start => />. rewrite /valid_pmsgs G.ST.P.allP => />H1. rewrite H1 => />. move :H. rewrite /ISet.mem iset_in_def /parties => />. rewrite G.ST.get_pmap => />. rewrite G.ST.get_pimap => />. rewrite G.ST.get_pzip !H0 => />. 
    rewrite Array.get_set_neqE => />*. rewrite Array.get_init => />*. rewrite hip => />. qed.

  lemma g_protocol_snd_def x ws cs :
    (G.protocol x ws cs).`2 = (G.g_protocol x ws cs).`2.
    rewrite /protocol /g_protocol => />*.
    have : G.protocol' x ws cs = G.ST.P.map snd3 ((G.g_protocol x ws cs).`1). rewrite -g_protocol_fst_def => />*. rewrite /protocol => />*. rewrite G.ST.P.map_snd_zip3 => />*. progress. rewrite H => />*. 
    (* output *)
    rewrite /protocol_end /local_protocol_end /g_protocol => />*. 
    rewrite G.ST.pmap_eqP => />y Hy. rewrite !G.ST.get_pimap => />*. rewrite !G.ST.get_pzip3 => />*. rewrite !G.ST.get_pmap !Hy => />*. rewrite !G.ST.get_pzip3 !Hy /snd3 => />*. rewrite G.ST.get_pmap => />*. rewrite G.ST.get_pzip !Hy => />*. rewrite /stateful_local_protocol_end => />*. rewrite !(G.get_send_messages x 1) => />*. rewrite /valid_messages G.ST.P.allP => />i Hi1 Hi2. rewrite G.ST.P.get_imap => />. rewrite G.valid_local_gate_start => />. 
    rewrite !(G.from_to_local_messages x 1) => />. rewrite /valid_pmsgs G.ST.P.allP => />i Hi1 Hi2. rewrite G.ST.P.get_map => />. rewrite G.ST.P.get_imap => />. 
    have : G.valid_pmsgs x 1 (G.from_local_messages (G.local_gate_start i x (G.GT.P.get (G.GT.P.zip ws cs) i).`1 (G.GT.P.get (G.GT.P.zip ws cs) i).`2)). rewrite G.valid_pmsgs_from => />. rewrite G.valid_local_gate_start => />. rewrite /valid_pmsgs G.ST.P.allP => />H1. rewrite H1 => />. move :Hy. rewrite /ISet.mem iset_in_def /parties => />.
    rewrite /get_local_state /get_local_state' /rounds !iseq_1 /update_local_state /init_local_state => />*. progress. rewrite /stateful_local_protocol_end => />*. 
    congr. congr. rewrite G.ST.pmap_eqP => />z Hz. rewrite !G.ST.get_pmap => />*. rewrite !G.ST.get_pinit !Hz => />*. rewrite G.GT.get_pmap => />*. rewrite Array.get_init => />*. 
    rewrite G.GT.get_pmap => />*. rewrite G.GT.get_pimap => />*. qed.

  lemma g_protocol_def x ws cs :
    (G.protocol x ws cs) = (G.g_protocol x ws cs).
    progress. rewrite (prod_id (G.protocol x ws cs)). rewrite g_protocol_fst_def => />*. rewrite g_protocol_snd_def => />*. qed.

  clone include WeakProofs with
    theory W = WG.
    

end WeakGateProofs.

theory WeakCircuitProofs.

  clone import WeakGateProofs as WGP.

  clone import WeakCircuit as WC with
    theory WG = WGP.WG
    proof *.
    realize corrupted_le. rewrite /corrupted_t /parties => />. rewrite WGP.WG.corrupted_le. qed.

  lemma circ_valid_randsE x cs :
    B.valid_rands x cs = B.circ_valid_rands x cs.
       rewrite /valid_rands /circ_valid_rands B.CT.P.allP => />*. rewrite eq_logical => />*. split.
       move => /> H i H1 H2.
       have : (B.consistent_rands x i i ((B.G.GT.P.get cs i)) ((B.G.GT.P.get cs i))). rewrite H => />*. rewrite /ISet.mem /ISet.iset !iset_in_def => />*. rewrite /consistent_rands => />. 
       move => /> H i j. move => />H1 H2.
       have : B.circ_valid_rand x ((B.G.GT.P.get cs i)). rewrite H => />. move :H1. rewrite /ISet.mem /ISet.iset iset_in_def => />. rewrite /circ_valid_rand => /> H3 H4. rewrite H3 => />. 
       have : B.circ_valid_rand x ((B.G.GT.P.get cs j)). rewrite H => />. move :H2. rewrite /ISet.mem /ISet.iset iset_in_def => />. rewrite /circ_valid_rand => /> H5 H6. rewrite -H3 H5 => />. qed.

  lemma get_local_state_take_circ i n n2 c ws rs ins :
    0 <= n /\ n <= n2 /\ n2 <= List.size c => B.get_local_state i n (take n2 c) ws rs ins = B.get_local_state i n c ws rs ins.
    rewrite /get_local_state /get_local_state' => />H H0 H1. move :H0 H. elim/natind:n => />n N1 N2 N3. rewrite !iseq_nil => />*.
    move => N4. rewrite !iseq_succ => />*. rewrite !foldl_rcons => />*. rewrite N2 => />*. smt(). clear N2. 
    rewrite /update_local_state => />*. congr. rewrite nth_take => />*. smt(). smt(). qed.

  lemma get_state_take_circ n n2 c ws rs ins :
    0 <= n /\ n <= n2 /\ n2 <= List.size c => B.get_state n (take n2 c) ws rs ins = B.get_state n c ws rs ins.
    rewrite /get_state => />*. congr. rewrite fun_ext => />*. rewrite fun_ext => />*. rewrite get_local_state_take_circ => />*. qed.

  lemma update_local_state_take_circ i n n2 c rs ins :
    0 <= n /\ n < n2 /\ n2 <= List.size c => B.update_local_state i n (take n2 c) rs ins = B.update_local_state i n c rs ins.
    rewrite /update_local_state => />*. rewrite nth_take => />*. smt(). qed.

  lemma get_local_state_nth_rand i n c ws rs ins :
    0 <= n /\ n <= List.size rs => nth witness rs n = head witness (B.get_local_state i n c ws rs ins).`2.
    rewrite /get_local_state /get_local_state' => />H H0. move :H0 H. move:rs. elim/natind:n => />n H. move => rs H0 H1. rewrite !iseq_nil => />*. rewrite /init_local_state => />*. rewrite(_:n=0). smt(). rewrite nth0_head => />*. 
    move => R rs H0 H1. rewrite !iseq_succ => />. rewrite foldl_rcons => />*. rewrite -nth_behead => />*. rewrite R => />*. clear R. rewrite size_behead => />*. smt(). congr. clear R.
    move :H H1 H0. elim/natind:n => />n. move => N0 N1 N2 N3. rewrite !iseq_nil => />*. 
    move => N0 N1 N2 N3 N4. rewrite !iseq_succ => />*. rewrite !foldl_rcons => />*. move :N1. rewrite /update_local_state => />N1. rewrite N1 => />*. clear N1. smt(). qed.

  op circ_get_local_state' (i:B.ST.party) (x:public_input) (acc:B.local_state * (B.ST.msg list) B.ST.pmap) : B.local_state * (B.ST.msg list) B.ST.pmap = 
    let go = fun (acc:B.local_state*_) (g:WG.G.Gate) =>
      let insr = B.ST.P.map (head witness) acc.`2 in
      let st = acc.`1 in
      let msgs = (WG.G.to_local_messages insr) in
      ((WG.G.local_gate_end i g st.`1 msgs,behead st.`2),B.ST.P.map behead acc.`2) in
    (foldl go acc x).

  op circ_get_local_state (i:B.ST.party) (x:public_input) (wi:B.ST.local_input) (ri:B.ST.local_rand) (insi:(B.ST.msg list) B.ST.pmap) : B.local_state = 
    (circ_get_local_state' i x (B.init_local_state i x wi ri,insi)).`1.

  lemma circ_get_local_state_cons' i g c acc :
    circ_get_local_state' i (cons g c) acc
      = circ_get_local_state' i c ((WG.G.local_gate_end i g acc.`1.`1 (WG.G.to_local_messages (B.ST.P.map (head witness) acc.`2)),behead acc.`1.`2),B.ST.P.map behead acc.`2).
    rewrite /circ_get_local_state' => />*. qed.

  lemma circ_get_local_state_rcons' i c g acc :
    circ_get_local_state' i (rcons c g) acc = 
      ((WG.G.local_gate_end i g (circ_get_local_state' i c acc).`1.`1 (WG.G.to_local_messages (B.ST.P.map (head witness) (circ_get_local_state' i c acc).`2)),behead (circ_get_local_state' i c acc).`1.`2),B.ST.P.map behead (circ_get_local_state' i c acc).`2).
    rewrite /circ_get_local_state' => />*. rewrite foldl_rcons => />*. qed.

  lemma circ_get_local_state_snd' i x (acc:_*_) :
    B.ST.P.all (fun _ ins => List.size x <= List.size ins) acc.`2 => (circ_get_local_state' i x acc).`2 = B.ST.P.map (drop (size x)) acc.`2.
    elim x acc => />acc. move => H. rewrite /circ_get_local_state' =>/>*. rewrite B.ST.pmap_eqP => />x. move => H0. rewrite !B.ST.get_pmap => />*. rewrite drop0 => />*. 
    move => l H0 acc0 H1. rewrite circ_get_local_state_cons' => />*. rewrite H0 => />*. move :H1. rewrite !B.ST.P.allP => />H1 j Hj1 Hj2. rewrite B.ST.get_pmap => />*. rewrite /ISet.mem iset_in_def => />*. rewrite size_behead => />*. have : 1 + size l <= size (B.ST.P.get acc0.`2 j). rewrite H1 => />*. progress. rewrite max_r => />*. have : 0 <= size l. rewrite size_ge0 //. smt(size_ge0). smt(size_ge0). rewrite B.ST.P.map_comp /(\o) => />*. rewrite B.ST.pmap_eqP => />x Hx. rewrite !B.ST.get_pmap => />*. rewrite drop_behead => />*. rewrite size_ge0 => />*. move :H1. rewrite B.ST.P.allP => />H1. have : 1 + size l <= size ((B.ST.P.get acc0.`2 x)). rewrite H1 => />*. move :Hx. rewrite /ISet.mem iset_in_def => />*. progress. rewrite (succ_gt0 (size l)) => />*. rewrite size_ge0 => />*. congr. algebra. qed.

  op circ_valid_msgs c xs = all_iseq (fun r => WGP.WG.G.valid_msg (nth witness c r) 0 (nth witness xs r)) (size c).
  op circ_valid_pmsgs c pxs = B.ST.P.all (fun i xs => circ_valid_msgs c xs) pxs.

  lemma circ_valid_msgs_nth c xs r :
    0 <= r < List.size c => r < List.size xs =>
    circ_valid_msgs (take (r+1) c) xs => WGP.WG.G.valid_msg (nth witness c r) 0 (nth witness xs r).
    move => Hip1 Hip2. rewrite /circ_valid_msgs all_iseqE allP => />H.
    have : WGP.WG.G.valid_msg (nth witness (take (r + 1) c) r) 0 (nth witness xs r). 
    rewrite H => />. rewrite in_iseq size_take => />. smt(). case (r + 1 < size c) => />. smt(). smt(). rewrite nth_take => />. smt(). smt(). qed.

  lemma circ_valid_msgs_cons x l m ms :
    circ_valid_msgs (cons x l) (cons m ms) = (WGP.WG.G.valid_msg x 0 m /\ circ_valid_msgs l ms).
    rewrite /circ_valid_msgs all_iseqE allP => />. rewrite eq_logical => />. split.
    move => H. rewrite all_iseqE allP => />. have : WGP.WG.G.valid_msg (if 0 = 0 then x else nth witness l (0 - 1)) 0 (if 0 = 0 then m else nth witness ms (0 - 1)). rewrite H => />. rewrite in_iseq => />. have : 0 <= size l. rewrite size_ge0 => />. smt(). simplify. move => H1. rewrite H1 => />y. rewrite in_iseq => />Hy1 Hy2. have : WGP.WG.G.valid_msg (if y+1 = 0 then x else nth witness l (y+1 - 1)) 0 (if y+1 = 0 then m else nth witness ms (y+1 - 1)). rewrite H => />. rewrite in_iseq => />. have : 0 <= size l. rewrite size_ge0 => />. smt(). have : ! (y+1=0). smt(). move => H2. rewrite !H2 => />. 
    rewrite all_iseqE allP => />H H1 y. rewrite in_iseq => />Hy1 Hy2. case (y=0) => />H2. rewrite H1 => />. rewrite in_iseq => />. smt(). qed.

  lemma circ_valid_pmsgs_get c pxs i :
     i \in B.ST.partyset =>
     circ_valid_pmsgs c pxs => circ_valid_msgs c (WGP.WG.G.ST.P.get pxs i).
     rewrite /circ_valid_pmsgs B.ST.P.allP => |>Hi H. rewrite H => |>. move :Hi. rewrite iset_in_def => />. qed.

  lemma circ_valid_msgs_take_le (n1 n2:int) x xs :
    0 <= n2 <= n1 =>
    circ_valid_msgs (take n1 x) xs => circ_valid_msgs (take n2 x) xs.
    rewrite /circ_valid_msgs !all_iseqE !allP => />H1 H H0 r.
    rewrite size_take => />. rewrite in_iseq => />Hr1 Hr2. 
    have : WGP.WG.G.valid_msg (nth witness (take n1 x) r) 0 (nth witness xs r). rewrite H0 => />. rewrite !size_take => />. smt(). rewrite !in_iseq => />. smt(). rewrite !nth_take => />. smt(). smt(). smt(). qed.

  lemma circ_valid_pmsgs_take_le (n1 n2:int) x xs :
    0 <= n2 <= n1 =>
    circ_valid_pmsgs (take n1 x) xs => circ_valid_pmsgs (take n2 x) xs.
    rewrite /circ_valid_pmsgs !B.ST.P.allP  => />H1 H H0 i Hi1 Hi2. have : circ_valid_msgs (take n1 x) (B.ST.P.get xs i). rewrite H0 => />. 
    move => H2. rewrite (circ_valid_msgs_take_le n1) => />. qed.

  lemma circ_get_local_state_take_succ i n x wi ri insi :
    0 <= n < List.size x => B.ST.P.all (fun _ ins => n < List.size ins) insi =>
    circ_valid_pmsgs (take (n+1) x) insi =>
    circ_get_local_state i (take (n+1) x) wi ri insi = 
      B.update_local_state i n x
        (WG.G.to_local_messages (B.ST.P.map (fun ins => nth witness ins n) insi))
        (circ_get_local_state i (take n x) wi ri insi).
    rewrite /circ_get_local_state => />H H0 H1 H2. rewrite !(take_nth witness) => />*. rewrite /update_local_state => />*. rewrite circ_get_local_state_rcons' => />*. rewrite /local_gate_end => />*. congr. rewrite /init_local_state => />*.  
    rewrite (WG.G.local_messages_eqP (nth witness x n) 0) => />*.
    rewrite WG.G.valid_local_messages_to => |>. rewrite /valid_pmsgs WGP.WG.G.ST.P.allP => />j Hj1 Hj2. rewrite WGP.WG.G.ST.P.get_map => />. rewrite circ_get_local_state_snd' => />. move :H1. rewrite !B.ST.P.allP => />H1 k Hk1 Hk2. rewrite size_take => />. rewrite H0 => />. have : n < size (B.ST.P.get insi k). rewrite H1 => />. smt(). rewrite WGP.WG.G.ST.P.get_map => />. rewrite size_take => />. rewrite H0 => />. rewrite -!nth0_head nth_drop => />. move :H1. rewrite B.ST.P.allP => />H1. have : n < size (B.ST.P.get insi j). rewrite H1 => />. smt(). rewrite circ_valid_msgs_nth => |>. move :H1. rewrite B.ST.P.allP => />H1. rewrite H1 => />. rewrite circ_valid_pmsgs_get => />. rewrite iset_in_def => />. 
    rewrite B.ST.pmap_eqP => />y Hy. rewrite !(WG.G.from_to_local_messages (nth witness x n) 0) => />*.
    rewrite /valid_pmsgs WGP.WG.G.ST.P.allP => />j Hj1 Hj2. rewrite WGP.WG.G.ST.P.get_map => />. rewrite circ_get_local_state_snd' => />. move :H1. rewrite !B.ST.P.allP => />H1 k Hk1 Hk2. rewrite size_take => />. rewrite H0 => />. have : n < size (B.ST.P.get insi k). rewrite H1 => />. smt(). rewrite WGP.WG.G.ST.P.get_map => />. rewrite size_take => />. rewrite H0 => />. rewrite -!nth0_head nth_drop => />. move :H1. rewrite B.ST.P.allP => />H1. have : n < size (B.ST.P.get insi j). rewrite H1 => />. smt(). rewrite circ_valid_msgs_nth => |>. move :H1. rewrite B.ST.P.allP => />H1. rewrite H1 => />. rewrite circ_valid_pmsgs_get => />. rewrite iset_in_def => />. 
    rewrite /valid_pmsgs WGP.WG.G.ST.P.allP => />j Hj1 Hj2. rewrite WGP.WG.G.ST.P.get_map => />. rewrite circ_valid_msgs_nth => |>. move :H1. rewrite B.ST.P.allP => />H1. have : n < size (B.ST.P.get insi j). rewrite H1 => />. rewrite /get => />H4. rewrite circ_valid_pmsgs_get => />. rewrite iset_in_def => />. 
    rewrite !B.ST.get_pmap => />*. rewrite circ_get_local_state_snd' => />*. rewrite size_take => />*. rewrite H0 => />*. move :H1. rewrite !B.ST.P.allP => />H1 k Hk1 Hk2. have : n < size (B.ST.P.get insi k). rewrite H1 => />. smt().
    rewrite B.ST.get_pmap => />*. rewrite size_take => />*. rewrite H0 => />*. rewrite -nth0_head nth_drop => />*. move :H1. rewrite B.ST.P.allP => />H1. have : n < size (B.ST.P.get insi y). rewrite H1 => />*. move :Hy. rewrite /ISet.mem iset_in_def => />*. smt(). qed.

  lemma equiv_circ_get_local_state szx i x wi ri insi :
    circ_valid_pmsgs x insi =>
    B.ST.P.all (fun _ ins => List.size x <= List.size ins <= szx) insi =>
      circ_get_local_state i x wi ri insi
      = B.get_local_state i (size x) x wi ri (B.ST.P.map (B.ST.rlist szx) insi).
    pose sz := size x. have : sz <= size x. smt().
    rewrite (_:x=take sz x). rewrite /sz take_size => />. rewrite size_take => />. rewrite /sz size_ge0 => />. move => H V H0. have : ! sz < size x. smt(size_ge0). progress. move: H. rewrite H1 => />H2.  
    clear H1. move :V H0 H2. elim/natind:sz =>/>n.
    move => N0 V N1 N2. rewrite !take_le0 => />*. rewrite /get_local_state /get_local_state' /circ_get_local_state => />*. rewrite !iseq_nil /init_local_state => />*. 
    move => N0 N1 V N2 N3. rewrite B.get_local_state_succ => />*. rewrite circ_get_local_state_take_succ => />*. smt(size_ge0). move :N2. rewrite !B.ST.P.allP => />N2 j Hj1 Hj2. have : n + 1 <= size (B.ST.P.get insi j) <= szx. rewrite N2 => />. smt(size_ge0). rewrite N1 => />*.
    rewrite (circ_valid_pmsgs_take_le (n+1)) => />. smt().
    move :N2. rewrite !B.ST.P.allP => />N2 j Hj1 Hj2. have : n + 1 <= size (B.ST.P.get insi j) <= szx. rewrite N2 => />. smt(size_ge0). smt(size_ge0).
    rewrite update_local_state_take_circ => />*. smt(). congr. rewrite /to_local_messages => />*. congr. rewrite B.ST.pmap_eqP => />y Hy. rewrite B.ST.get_prget Hy => />*. rewrite !B.ST.get_pmap => />*. rewrite B.ST.get_rlist => />*.
    move :N2. rewrite B.ST.P.allP => />N2. have : n + 1 <= size ((B.ST.P.get insi y)) <= szx. rewrite N2 => />*. move :Hy. rewrite /ISet.mem iset_in_def => />*. smt(size_ge0). move :N2. rewrite B.ST.P.allP => />N2. have : n + 1 <= size ((B.ST.P.get insi y)) <= szx. rewrite N2 => />*. move :Hy. rewrite /ISet.mem iset_in_def => />*. smt(size_ge0). rewrite !get_local_state_take_circ => />. smt(size_ge0). smt(). qed.

  lemma size_circ_protocol_fst' c ws rs i j :
    i \in P.ST.partyset /\ j \in P.ST.partyset => 
      size ((P.ST.P.get ((P.ST.P.get ((B.circ_protocol' c ws rs)).`1 i)) j)) = size c.
    progress. move: ws rs. elim c => />. rewrite P.ST.get_ppinit /ISet.mem H => />*. rewrite P.ST.get_pinit /ISet.mem H0 => />*.
    move => x l H1 ws rs. rewrite /ppcons P.ST.get_pmerge /ISet.mem H /pcons => />*. rewrite P.ST.get_pmerge /ISet.mem H0 => />*. rewrite H1 => />*. qed.

  lemma r_get_circ_protocol' c ws rs i:
    i \in P.ST.partyset =>
      (B.ST.P.all (fun (_ : int) (ins : B.ST.msg list) => List.size c = size ins) ((B.ST.P.get ((B.circ_protocol' c ws rs)).`1 i))).
    rewrite B.ST.P.allP => />. progress. rewrite !size_circ_protocol_fst' => />*. rewrite iset_in_def => />*. qed.

  lemma get_st_gst (xs:'a B.ST.P.arrayN) i:
    B.ST.P.get xs i = WGP.WG.G.ST.P.get xs i. progress. qed.

  lemma get_st_ggt (xs:'a B.ST.P.arrayN) i:
    B.ST.P.get xs i = WGP.WG.G.GT.P.get xs i. progress. qed.

  lemma get_ct_ggt (xs:'a B.ST.P.arrayN) i:
    B.CT.P.get xs i = WGP.WG.G.GT.P.get xs i. progress. qed.

  lemma valid_circ_protocol' c ws rs i :
    i \in P.ST.partyset =>
    circ_valid_pmsgs c (B.ST.P.get (B.circ_protocol' c ws rs).`1 i).
    rewrite /circ_valid_pmsgs B.ST.P.allP => |>Hi j Hj1 Hj2. elim c ws rs => |>. 
    rewrite B.ST.get_ppinit /mem -memE Hi /circ_valid_msgs all_iseqE allP => |>r. rewrite in_iseq => |>Hr1 Hr2. have : false. smt(). progress.
    move => x l V ws rs. rewrite /ppcons B.ST.get_ppinit /ISet.mem Hi => |>. rewrite B.ST.get_pinit => |>. have : mem j B.ST.partyset. rewrite /ISet.mem iset_in_def => |>. move => Hj. rewrite Hj => |>. rewrite circ_valid_msgs_cons => |>.
    have : B.valid_messages (cons x l) 0 (B.stateful_protocol_round 0 (cons x l) (B.CT.P.zip ws rs)). rewrite B.valid_stateful_protocol_round => |>. move => V1. have : B.valid_messages (cons x l) 0 (B.send_messages (B.stateful_protocol_round 0 (cons x l) (B.CT.P.zip ws rs))). rewrite B.valid_send_messages => |>. move => V2. have : B.valid_ppmsgs (cons x l) 0 (B.from_messages (B.send_messages (B.stateful_protocol_round 0 (cons x l) (B.CT.P.zip ws rs)))). rewrite B.valid_ppmsgs_from => |>. rewrite /valid_ppmsgs B.ST.P.allP => |>V3. have : B.valid_pmsgs (cons x l) 0 (B.ST.P.get (B.from_messages (B.send_messages (B.stateful_protocol_round 0 (cons x l) (B.CT.P.zip ws rs)))) i). rewrite V3 => />. move :Hi. rewrite iset_in_def => />. rewrite /valid_pmsgs B.ST.P.allP => |>V4. have : B.valid_msg (cons x l) 0 (B.ST.P.get (B.ST.P.get (B.from_messages (B.send_messages (B.stateful_protocol_round 0 (cons x l) (B.CT.P.zip ws rs)))) i) j). rewrite V4 => |>. rewrite /valid_msg => />. rewrite V => />. qed.

  lemma circ_protocol_get_state' c ws rs i :
    i \in P.ST.partyset =>
      (B.ST.P.get ((B.circ_protocol' c ws rs)).`2.`2 i)
      = ((B.ST.P.get ((P.get_state (size c) c ws rs ((WG.G.GT.P.map ((WG.G.GT.P.map (WG.G.GT.rlist (size c)) )) ((B.circ_protocol' c ws rs)).`1)))) i)).`1.
    rewrite /get_state => |>Hi. rewrite B.ST.get_pimap => |>. rewrite !B.ST.get_pzip3 => |>. have : mem i B.ST.partyset. rewrite /ISet.mem => |>. move => memi. rewrite !memi => |>. rewrite B.ST.get_pmap => |>. rewrite -equiv_circ_get_local_state => |>. rewrite valid_circ_protocol' => |>. 
    have : B.ST.P.all (fun (_ : int) (ins : B.ST.msg list) => size c = size ins) (B.ST.P.get (fst3 (B.circ_protocol' c ws rs)) i). rewrite r_get_circ_protocol' => |>. rewrite !B.ST.P.allP => |>H j Hj1 Hj2. rewrite !(H j) => />. 
    elim c ws rs => />. progress. rewrite H => />*. clear H. rewrite /circ_get_local_state circ_get_local_state_cons' => />*. congr. congr. congr. 
    rewrite /init_local_state /g_protocol => />*. rewrite B.ST.get_pmap => />*. rewrite /ppcons B.ST.get_ppinit memi => />*. rewrite !B.ST.get_pimap => />*. rewrite !B.ST.get_pzip !memi => />*. split. 
    rewrite /local_gate_end => />*. congr. rewrite !get_st_gst (WGP.WG.G.get_send_messages x 0) => />*.
    rewrite /valid_messages WGP.WG.G.ST.P.allP => />j Hj1 Hj2. rewrite WGP.WG.G.ST.P.get_imap => />. rewrite !WGP.WG.G.ST.P.get_zip !andabP !andaP => />. rewrite WGP.WG.G.ST.P.get_map => />. rewrite WGP.WG.G.valid_local_gate_start => />.
    rewrite /to_local_messages => />*. congr. rewrite B.ST.pmap_eqP => />y Hy. rewrite !B.ST.get_pmap => />*. rewrite !B.ST.get_pinit !Hy /from_messages => />*. rewrite !WGP.WG.G.GT.get_pmap => />*. rewrite WGP.WG.G.GT.get_pzip !Hy /stateful_protocol_round /stateful_local_protocol_round => />*. rewrite /from_local_messages => />*. rewrite -!get_st_ggt (B.get_send_messages (cons x l) 0) => />*.
    rewrite /valid_messages B.ST.P.allP => />j Hj1 Hj2. rewrite B.ST.P.get_imap => />. rewrite !B.ST.P.get_zip !andabP !andaP => />. rewrite /valid_local_messages => />. rewrite WGP.WG.G.valid_local_gate_start => />.
    rewrite B.ST.P.imap_comp /(\o) => />*. rewrite /from_local_messages => />*. rewrite (_:WGP.WG.G.from_local_messages=B.from_local_messages) => />*. rewrite (B.from_to_local_messages (cons x l) 0) => />*.
    rewrite /valid_pmsgs B.ST.P.allP => />j Hj1 Hj2. rewrite !B.ST.P.get_imap /valid_msg => />. rewrite !B.ST.P.get_zip !andabP !andaP => />. have : WGP.WG.G.valid_local_messages x 0 (WGP.WG.G.local_gate_start j x (B.ST.P.get ws j) (head witness (B.ST.P.get rs j)) ). rewrite WGP.WG.G.valid_local_gate_start => |>. move => V1. have : WGP.WG.G.valid_pmsgs x 0 (WGP.WG.G.from_local_messages (WGP.WG.G.local_gate_start j x (B.ST.P.get ws j) (head witness (B.ST.P.get rs j)))). rewrite WGP.WG.G.valid_pmsgs_from => |>. rewrite /valid_pmsgs WGP.WG.G.ST.P.allP => />H. rewrite H => />. move :Hi. rewrite iset_in_def => />.  
    rewrite !B.ST.get_pimap => />*. rewrite /get. congr. rewrite (_:WGP.WG.G.from_local_messages=B.from_local_messages) => />*. congr. rewrite -!get_st_ggt B.ST.get_pzip !Hy => />*. rewrite B.ST.pmap_eqP => />y Hy. rewrite B.ST.get_pmap => />*. rewrite !B.ST.get_pinit Hy => />*. qed.

  lemma circ_protocol_thr' c ws rs :
    ((B.circ_protocol' c ws rs)).`2.`2
      = B.ST.P.map fst ((P.get_state (size c) c ws rs ((WG.G.GT.P.map ((WG.G.GT.P.map (WG.G.GT.rlist (size c)))) ((B.circ_protocol' c ws rs)).`1)))).
    rewrite B.ST.pmap_eqP => />x Hx. rewrite B.ST.get_pmap => />*. rewrite circ_protocol_get_state' => />*. qed.

  lemma circ_protocol_cons' x l ws cs :
    (B.circ_protocol' (x :: l) ws cs) = (B.ST.ppcons (B.ST.ppswap (B.from_messages (B.stateful_protocol_round 0 (x::l) (B.ST.P.zip ws cs)))) (B.circ_protocol' l (WG.G.protocol x ws (B.ST.P.map (head witness) cs)).`2 (B.ST.P.map behead cs)).`1, (B.ST.pcons (B.ST.P.map (head witness) cs) (B.circ_protocol' l (WG.G.protocol x ws (B.ST.P.map (head witness) cs)).`2 (B.ST.P.map behead cs)).`2.`1,(B.circ_protocol' l (WG.G.protocol x ws (B.ST.P.map (head witness) cs)).`2 (B.ST.P.map behead cs)).`2.`2)).
   rewrite /WG.G.protocol. rewrite WGP.g_protocol_snd_def => />*. rewrite /thr3 /g_protocol /pcons => />*. rewrite B.CT.P.map_thr_zip3 => />*. rewrite !(B.ppswap_from_messages (cons x l) 0) => />*.
   rewrite B.valid_stateful_protocol_round => />. qed.

  lemma circ_protocol_snd_cons x l ws cs :
    (B.circ_protocol (x :: l) ws cs).`2 = (B.circ_protocol l (WG.G.protocol x ws (B.ST.P.map (head witness) cs)).`2 (B.ST.P.map behead cs)).`2.
    rewrite /circ_protocol. rewrite circ_protocol_cons' => />*. qed.

  lemma prset_gt_st (xs:'a B.ST.prmap) i x :
    WGP.WG.G.GT.prset xs i x = B.ST.prset xs i x. progress. qed.

  lemma equiv_circuit_round x l ys c cs :
    B.ST.P.map (B.ST.P.map (fun rs => Array.get rs 0) \o snd3) (WG.G.protocol x ys c).`1
      = B.ST.ppswap (B.from_messages (B.stateful_protocol_round 0 (cons x l) (B.ST.P.zip ys (B.ST.pcons c cs)))).
    rewrite /stateful_protocol_round /protocol => />*. rewrite B.ST.ppmap_eqP => />y z Hy Hz. rewrite !B.ST.get_pmap /(\o) /snd3 => />*. rewrite /ppswap !B.ST.get_ppinit !Hy => />*. rewrite B.ST.get_pmap => />*. rewrite !B.ST.get_pinit !Hy !Hz => />*. rewrite WGP.WG.G.GT.get_pzip Hy => />*. rewrite /protocol' /protocol'' /stateful_local_protocol_round /rounds iseq_1 => />*. rewrite WGP.WG.G.GT.get_pprset Hy => />*. rewrite /ppswap WGP.WG.G.GT.get_ppinit Hy => />*. rewrite WGP.WG.G.GT.get_ppinit Hy => />*. 
    rewrite prset_gt_st B.ST.get_prset Hz => />*. rewrite !B.ST.get_pinit Hz => />*. rewrite Array.get_set_eqE => />*. rewrite size_init => />*. rewrite /protocol_round /local_protocol_round => />*. rewrite WGP.WG.G.GT.get_pimap => />*. rewrite !WGP.WG.G.GT.get_pzip3 !Hz => />*. rewrite /from_messages get_ct_ggt => />*. congr. rewrite B.CT.get_pmap => />*. rewrite B.CT.get_pimap => />*. rewrite WGP.WG.G.GT.get_pprempty Hz => />*. rewrite /stateful_local_protocol_round => />*. rewrite /get_local_state /get_local_state' iseq_nil /init_local_state => />*. rewrite B.CT.get_pzip Hz /pcons => />*. rewrite B.CT.get_pmerge Hz => />*. qed.

  op circ_prot_fst_cons prev g ws rs ins = P.ST.pprcons ins
    (P.ST.P.map (transpose P.ST.prget 0 \o snd3) (WG.G.g_protocol g (B.circ_protocol' prev ws rs).`2.`2 (B.CT.P.map (fun r => nth witness r (size prev)) rs)).`1). 

  lemma get_wgt_st (xs:'a B.ST.P.arrayN) i :
    WG.G.GT.P.get xs i = B.ST.P.get xs i. progress. qed.

  lemma get_wgt_pst (xs:'a B.ST.P.arrayN) i :
    WG.G.GT.P.get xs i = P.ST.P.get xs i. progress. qed.

  lemma get_wwgt_ct (xs:'a B.ST.P.arrayN) i :
    WGP.WG.G.GT.P.get xs i = B.CT.P.get xs i. progress. qed.

  lemma get_wst_st (xs:'a B.ST.P.arrayN) i :
    WG.G.ST.P.get xs i = B.ST.P.get xs i. progress. qed.

  lemma ppcat_ct_st (xs ys : ('a list) P.ST.ppmap) :
    B.CT.ppcat xs ys = P.ST.ppcat xs ys. progress. qed.

  lemma pprcons_ct_st (xs : ('a list) P.ST.ppmap) x :
    B.CT.pprcons xs x = P.ST.pprcons xs x. progress. qed.

  lemma circ_stateful_protocol_round0 x l st :
    B.stateful_protocol_round 0 (cons x l) st = B.stateful_protocol_round 0 [x] st.
    rewrite /stateful_protocol_round => />*. qed.

  lemma circ_protocol_fst_rcons' c g ws rs :
    (B.circ_protocol' (rcons c g) ws rs).`1 = circ_prot_fst_cons c g ws rs (B.circ_protocol' c ws rs).`1.
    elim c ws rs => />ws rs. rewrite /circ_prot_fst_cons => />*. rewrite -pprcons_ct_st. rewrite B.CT.ppmap_eqP /ppcons /pprcons => />x y Hx Hy. rewrite !B.CT.P.get_merge => />*. have : 0 <= x < B.CT.P.size. move :Hx. rewrite /ISet.mem iset_in_def => />*. move => Hx'. rewrite !Hx' => />*. rewrite /pcons /prcons => />*. have : 0 <= y < B.CT.P.size. move :Hy. rewrite /ISet.mem iset_in_def => />*. move => Hy'. rewrite !B.CT.P.get_merge !Hy' => />*. rewrite !B.CT.get_ppinit !Hx => />*. rewrite !B.CT.get_pinit !Hy !Hx /snd3 => />*. rewrite -!get_st_ggt (B.get_send_messages [g] 0) => />*.
    rewrite B.valid_stateful_protocol_round => />. 
    rewrite (B.from_to_local_messages [g] 0) => />*.
    rewrite /valid_pmsgs B.ST.P.allP => />j Hj1 Hj2. rewrite B.ST.P.get_map => />. have : B.valid_messages [g] 0 (B.stateful_protocol_round 0 [g] (B.CT.P.zip ws rs)). rewrite B.valid_stateful_protocol_round => />. move => V1. have : B.valid_pmsgs [g] 0 (B.from_local_messages (B.ST.P.get (B.stateful_protocol_round 0 (cons g []) (B.CT.P.zip ws rs)) j)). rewrite B.valid_pmsgs_from => />. rewrite B.valid_messages_get => />. rewrite /ISet.mem iset_in_def => />. rewrite B.valid_pmsgs_get => />. move :Hx'. progress. rewrite B.valid_pmsgs_from => />. rewrite B.valid_messages_get => />. rewrite /ISet.mem iset_in_def => />. 
    rewrite B.CT.P.get_map /g_protocol /stateful_protocol_round => />*. rewrite B.CT.P.get_imap => />*. rewrite B.CT.P.get_zip !Hy' => />*. rewrite B.ST.P.get_zip3 Hx' => />*. rewrite B.ST.P.get_map => />*. move :Hx'. progress. rewrite B.CT.P.get_map => />*. rewrite Array.get_init => />*. rewrite !get_st_gst (WGP.WG.G.get_send_messages g 0) => />*.
    rewrite /valid_messages WGP.WG.G.ST.P.allP => />j Hj1 Hj2. rewrite WGP.WG.G.ST.P.get_imap => />. rewrite !WGP.WG.G.ST.P.get_zip !andabP !andaP => />. rewrite WGP.WG.G.ST.P.get_map => />. rewrite WGP.WG.G.valid_local_gate_start => />. 
    rewrite (WGP.WG.G.from_to_local_messages g 0) => />*.
    rewrite /valid_pmsgs WGP.WG.G.ST.P.allP => />j Hj1 Hj2. rewrite WGP.WG.G.ST.P.get_map => />. rewrite WGP.WG.G.ST.P.get_imap => />. rewrite !WGP.WG.G.ST.P.get_zip !andabP !andaP => />. rewrite WGP.WG.G.ST.P.get_map => />. have : WGP.WG.G.valid_local_messages g 0 (WGP.WG.G.local_gate_start j g (WGP.WG.G.ST.P.get ws j) (nth witness (WGP.WG.G.ST.P.get rs j) 0)). rewrite WGP.WG.G.valid_local_gate_start => />. move => V1. have : WGP.WG.G.valid_pmsgs g 0 (WGP.WG.G.from_local_messages (WGP.WG.G.local_gate_start j g (WGP.WG.G.ST.P.get ws j) (nth witness (WGP.WG.G.ST.P.get rs j) 0))). rewrite WGP.WG.G.valid_pmsgs_from => />. move => V2. rewrite WGP.WG.G.valid_pmsgs_get => />. move :Hx'. progress.
    rewrite B.CT.P.get_map => />*. rewrite -!get_wwgt_ct WGP.WG.G.GT.P.get_imap => />*. move :Hy'. progress. rewrite /stateful_local_protocol_round => />*. rewrite !WGP.WG.G.GT.P.get_zip !Hy' => />*. rewrite WGP.WG.G.GT.P.get_map => />*. move :Hy'. progress.
    congr. rewrite /from_local_messages /local_gate_start => />. congr. congr. rewrite nth0_head => />. 
    move => H ws0 rs0.  
    rewrite H => />*. rewrite /circ_prot_fst_cons => />*. clear H.
    rewrite B.CT.ppcons_pprcons => />*. rewrite pprcons_ct_st => />*. congr. congr. congr. congr. rewrite circ_stateful_protocol_round0 => />*. 
    congr. congr. congr. rewrite B.CT.P.map_comp /(\o) => />*. congr. rewrite fun_ext => />x. rewrite fun_ext => />y. case y => />l l0. have : !(1 + size rs = 0). have : 0 <= size rs. rewrite size_ge0. smt(). progress. rewrite H => />*. qed.

  lemma circ_protocol_take_rs' c ws rs :
    B.circ_protocol' c ws rs = B.circ_protocol' c ws (B.CT.P.map (take (size c)) rs).
    elim c ws rs => />x l H ws rs. progress. 
    congr. congr. congr. rewrite /stateful_protocol_round => />*. rewrite B.ST.pmap_eqP => />y Hy. have : 0 <= y < B.ST.P.size. move :Hy. rewrite /ISet.mem iset_in_def => />*. move => ydom. rewrite !B.ST.P.get_imap => />*. rewrite /stateful_local_protocol_round => />*. rewrite !B.ST.P.get_zip !ydom => />*. rewrite B.ST.P.get_map => />*. congr. rewrite head_take_some => />*. have : 0 <= size l. rewrite size_ge0 => />. smt(). 
    rewrite H => />*. rewrite !B.CT.P.map_comp /(\o) => />*. congr. congr. congr. congr. congr. rewrite fun_ext => />y. rewrite fun_ext => />z. rewrite head_take_some => />*. have : 0 <= size l. rewrite size_ge0 => />. smt(). congr. rewrite fun_ext => />y. rewrite fun_ext => />z. rewrite take_behead => />*. rewrite size_ge0 => />*. 
    congr. congr. congr. congr. rewrite B.CT.P.map_comp /(\o) => />*. congr. rewrite fun_ext => />y. rewrite fun_ext => />z. rewrite head_take_some => />*. have : 0 <= size l. rewrite size_ge0 => />. smt(). 
    rewrite H => />*. rewrite !B.CT.P.map_comp /(\o) => />*. congr. congr. congr. congr. congr. congr. rewrite fun_ext => />y. rewrite fun_ext => />z. rewrite head_take_some => />*. have : 0 <= size l. rewrite size_ge0 => />. smt().
    congr. rewrite fun_ext => />y. rewrite fun_ext => />z. rewrite take_behead => />*. rewrite size_ge0 => />*. 
    congr. rewrite H => />*. rewrite !B.CT.P.map_comp /(\o) => />*. congr. congr. congr. congr. congr. rewrite fun_ext => />y. rewrite fun_ext => />z. rewrite head_take_some => />*. have : 0 <= size l. rewrite size_ge0 //. smt().
    congr. rewrite fun_ext => />y. rewrite fun_ext => />z. rewrite take_behead => />*. rewrite size_ge0 => />*. qed.

  lemma circ_protocol_take_rs_n' c ws rs n :
    n = List.size c =>
    B.circ_protocol' c ws rs = B.circ_protocol' c ws (B.CT.P.map (take n) rs).
    progress. rewrite circ_protocol_take_rs' => />*. qed.

  lemma circ_protocol_fst_take_succ' c ws rs n :
    0 <= n /\ n < List.size c => (B.circ_protocol' (take (n + 1) c) ws rs).`1 = P.ST.pprcons
      (B.circ_protocol' (take n c) ws rs).`1
      (P.ST.P.map (transpose P.ST.prget 0 \o snd3) (WG.G.g_protocol (nth witness c n) (B.circ_protocol' (take n c) ws (B.CT.P.map (take n) rs)).`2.`2 (B.CT.P.map (fun r => nth witness r n) rs)).`1).
     progress. rewrite (take_nth witness) => />*. rewrite circ_protocol_fst_rcons' => />*.
    rewrite /circ_prot_fst_cons => />*. rewrite size_take => />*. rewrite H0 => />*.
    congr. congr. congr. congr. rewrite circ_protocol_take_rs' => />*. congr. congr. rewrite size_take => />*. rewrite H0 => />*. qed.

  lemma get_state_rlist (n n1 n2 n3:int) c ws rs :
    n <= n1 => n <= n2 => n <= n3 => n <= List.size c => n3 <= n1 => n3 <= n2 =>
    B.get_state n c ws rs (WG.G.GT.P.map (fun xs => WG.G.GT.P.map (WG.G.GT.rlist n1) xs) (B.circ_protocol' (take n3 c) ws rs).`1) =
    B.get_state n c ws rs (WG.G.GT.P.map (fun xs => WG.G.GT.P.map (WG.G.GT.rlist n2) xs) (B.circ_protocol' (take n3 c) ws rs).`1).
    move => N1 N2 N3 N4 N5 N6. rewrite /get_state => />. rewrite B.ST.pmap_eqP => />k Hk. rewrite !B.ST.get_pimap => />. rewrite !B.ST.get_pzip3 !Hk => />. rewrite !B.ST.get_pmap => />. rewrite /get_local_state /get_local_state' => />. move :N1 N2 N3 N4 N5 N6. elim/natind:n => />n.
    move => N0 N1 N2 N3 N4 N5 N6. rewrite !iseq_nil => />.
    move => N0 R N1 N2 N3 N4 N5 N6. rewrite !iseq_succ => />. rewrite !foldl_rcons => />. rewrite R => />. smt(). smt(). smt(). smt(). clear R. congr. congr. rewrite /prget B.CT.pmap_eqP => />x Hx. rewrite !B.CT.get_pinit !Hx => />. rewrite !B.CT.get_pmap => />.
    rewrite !WG.G.GT.get_rlist => />. rewrite size_circ_protocol_fst' => />. rewrite size_take => />. smt(). smt(). rewrite size_circ_protocol_fst' => />. rewrite size_take => />. smt(). smt(). rewrite size_circ_protocol_fst' => />. rewrite size_take => />. smt(). smt(). rewrite size_circ_protocol_fst' => />. rewrite size_take => />. smt(). smt(). qed.

  lemma equiv_circ_protocol_stateful_fst' c ws rs n :
    P.valid_rands c rs /\ 0 <= n <= WC.B.ST.rounds c =>
      WG.G.GT.P.map (WG.G.GT.P.map (WG.G.GT.rlist (WC.B.ST.rounds c))) (WC.B.circ_protocol' (take n c) ws (B.CT.P.map (take n) rs)).`1 = (WC.B.stateful_protocol'' c (WG.G.GT.pprempty (WC.B.ST.rounds c) witness) (WC.B.init_state c ws rs) n).`1.
    rewrite /stateful_protocol' => />H H0 H1. move :H H0 H1. elim/natind:n ws rs => />n H. 
    (*nil*)
    move => ws rs H0 H1 H2.
    rewrite /stateful_protocol'' !iseq_nil => />*. rewrite WG.G.GT.ppmap_eqP => />x y Hx Hy. rewrite !WG.G.GT.get_pmap => />*. rewrite WG.G.GT.get_pmap /stateful_protocol''' => />*. rewrite WG.G.GT.get_pprempty Hx => />*. rewrite WG.G.GT.get_prempty Hy => />*. rewrite (_:n = 0). smt(). rewrite take0 => />*. rewrite WG.G.GT.get_ppinit Hx => />*. rewrite WG.G.GT.get_pinit Hy => />*. rewrite /rlist iseq_nil => />*.
    (*cons*)
    move => R ws rs H0 H1 H2.
    rewrite (_: (B.stateful_protocol'' c (WG.G.GT.pprempty (B.ST.rounds c) witness) (B.init_state c ws rs) (n + 1)) = ((P.stateful_protocol'' c (P.ST.pprempty (B.ST.rounds c) witness) ((P.init_state c ws rs)) (n + 1))) ). progress. rewrite P.stateful_protocol_fst_succ'' => />*. rewrite (_:  ((P.stateful_protocol'' c (P.ST.pprempty (B.ST.rounds c) witness) ((P.init_state c ws rs)) n)) = ((B.stateful_protocol'' c (WG.G.GT.pprempty (B.ST.rounds c) witness) ((B.init_state c ws rs)) n)) ). progress. rewrite -R => />*. smt().
    rewrite (_: ((B.stateful_protocol'' c (WG.G.GT.pprempty (B.ST.rounds c) witness) ((B.init_state c ws rs)) n)) = ((P.stateful_protocol'' c (P.ST.pprempty (B.ST.rounds c) witness) ((P.init_state c ws rs)) n)) ). progress. rewrite -P.equiv_stateful_protocol'' => />*. smt(). rewrite (_: ((P.stateful_protocol'' c (P.ST.pprempty (B.ST.rounds c) witness) ((P.init_state c ws rs)) n)) = ((B.stateful_protocol'' c (WG.G.GT.pprempty (B.ST.rounds c) witness) ((B.init_state c ws rs)) n)) ). progress. rewrite -R => />*. smt(). clear R.
    rewrite circ_protocol_fst_take_succ' => />*. smt(). rewrite WG.G.GT.ppmap_eqP => />x y Hx Hy. rewrite !WG.G.GT.get_pmap /pprcons => />*. rewrite WG.G.GT.get_pmap => />*. rewrite WG.G.GT.get_pmerge Hx /prcons => />*. rewrite WG.G.GT.get_pmerge Hy => />*. rewrite WG.G.GT.get_pmap /(\o) => />*. rewrite WG.G.GT.get_prget Hy /snd3 => />*. rewrite !get_wgt_pst P.ST.get_pprset => />*. rewrite P.ST.get_pmap => />*. rewrite /g_protocol /stateful_protocol_round !Hx => />*. rewrite P.ST.get_pzip3 Hx => />*. rewrite !P.ST.get_pmap => />*. rewrite P.ST.get_pmap => />*. rewrite Array.get_init => />*.
    rewrite P.ST.get_prset Hy => />*. rewrite WG.G.GT.rlist_rcons. rewrite P.ST.get_pmap => />*. congr. rewrite /rlist. congr. rewrite fun_ext => />zs. rewrite fun_ext => />z. congr. congr. congr. congr. rewrite circ_protocol_take_rs' => />*. rewrite !B.CT.P.map_comp /(\o) => />*. congr. congr. congr. rewrite fun_ext => />w. rewrite fun_ext => />k. rewrite size_take => />*. have : n < size c. smt(size_ge0). move => N. rewrite N => />*. rewrite take_min => />*. have : n = min n (n+1). smt(). move => N1. rewrite -N1 => />*. 
    rewrite size_circ_protocol_fst' => />*. rewrite size_take => />*. have : n < size c. smt(). move => N. rewrite N => />*. rewrite size_circ_protocol_fst' => />*. rewrite size_take => />*. rewrite N => />*. rewrite size_circ_protocol_fst' => />*. rewrite size_take => />*. have : n < size c. smt(). move => N1. rewrite N1 => />*. 
    congr. rewrite (_: WGP.WG.G.from_local_messages = B.from_local_messages). progress. congr. congr. rewrite (_: WGP.WG.G.send_messages = P.send_messages ). progress. congr. rewrite B.ST.pmap_eqP => />z Hz. rewrite !B.ST.get_pimap /stateful_local_protocol_round => />*. rewrite (_:WGP.WG.G.local_gate_start=B.G.local_gate_start). progress. congr. rewrite B.ST.get_pzip Hz => />*. rewrite B.CT.P.map_comp. rewrite take_min' => />*. rewrite (_:min n (n+1)=n) => />*. smt(). rewrite -!circ_protocol_take_rs_n' => />*. rewrite size_take => />*. have : n < size c. smt(size_ge0). move => N. rewrite N => />*. 
    rewrite circ_protocol_get_state' => />*. rewrite size_take => />*. have : n < size c. smt(). move => N. rewrite N => />*. congr. congr. rewrite (_:P.get_state=B.get_state). progress. rewrite get_state_take_circ => />*. smt(). rewrite (get_state_rlist n n (B.ST.rounds c) n) => />. smt(). smt(). smt(). 
    rewrite B.ST.get_pzip Hz => />. rewrite !B.ST.get_pmap => />. rewrite nth_take => />. smt(). rewrite /get_state => />. rewrite B.ST.get_pimap => />. rewrite !B.ST.get_pzip3 !Hz => />. rewrite !B.ST.get_pmap => />. rewrite -(get_local_state_nth_rand) => />. move :H0. rewrite /valid_rands => />H0. have : B.consistent_rands c z z (B.ST.P.get rs z) (B.ST.P.get rs z). rewrite H0 => />.
    rewrite /consistent_rands => />. move => H3 H4. rewrite -H3 => />. smt(). qed.
  
  lemma equiv_circ_protocol_stateful_snd c ws rs :
    P.valid_rands c rs =>
      (WC.B.circ_protocol c ws rs).`2 = (WC.B.stateful_protocol c ws rs).`2.
    progress. rewrite /circ_protocol /stateful_protocol /stateful_protocol' /stateful_protocol_end /stateful_local_protocol_end => />*. rewrite B.ST.pmap_eqP => /> x Hx. rewrite circ_protocol_get_state' => />*. rewrite -B.equiv_stateful_protocol'' => />*. rewrite /rounds => />*. rewrite (size_ge0) => />*. rewrite B.ST.get_pmap => />*. congr. congr. 
    rewrite(_: ((B.stateful_protocol'' c (B.ST.pprempty (B.ST.rounds c) witness) ((B.init_state c ws rs)) ((B.ST.rounds c)))) = ((B.stateful_protocol'' c (WG.G.GT.pprempty (B.ST.rounds c) witness) ((B.init_state c ws rs)) ((B.ST.rounds c)))) ). progress. rewrite -equiv_circ_protocol_stateful_fst' => />*. rewrite /rounds => />*. rewrite size_ge0 => />*. rewrite /rounds take_size => />*. rewrite -circ_protocol_take_rs' => />*. qed.

  lemma equiv_circ_protocol_thr' c ws rs i :
    i \in B.ST.partyset /\ P.valid_rands c rs =>
      B.ST.P.get (B.circ_protocol' c ws rs).`2.`1 i = B.ST.P.get rs i.
    rewrite /valid_rands /circ_valid_rands => />H H0.
    have : B.consistent_rands c i i (B.ST.P.get rs i) (B.ST.P.get rs i). rewrite H0 => />. rewrite /consistent_rands => />. clear H0.
    move:ws rs. elim:c => />.
    move => r H0. rewrite lsame_nil => />H1. rewrite B.ST.get_pinit /ISet.mem H => />. rewrite H1 //. 
    move => x l R ws rs H0 H1. rewrite /pcons B.ST.get_pmerge /ISet.mem H => />*. rewrite B.ST.get_pmap /thr3 => />*. rewrite R => />*. rewrite B.ST.get_pmap => />*. rewrite size_behead -H0 => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite B.ST.get_pmap => />. 
    rewrite (lsame_cons_left2 _ x) => />*. rewrite B.ST.get_pmap => />*. rewrite /g_protocol => />*. rewrite B.ST.get_pzip3 /ISet.mem H => />*. rewrite B.ST.get_pmap => />*. rewrite head_behead => />*. rewrite -size_eq0 => />*. rewrite -H0 => />*. have : 0 <= size l. rewrite size_ge0 //. smt(). qed.

  lemma equiv_circ_protocol_stateful c ws rs :
    P.valid_rands c rs =>
      (WC.B.circ_protocol c ws rs) = (WC.B.stateful_protocol c ws rs).
    rewrite eq2 => |>H. rewrite equiv_circ_protocol_stateful_snd => |>*.
    rewrite /circ_protocol /stateful_protocol /stateful_protocol' => |>*.
    rewrite (_: ((B.stateful_protocol'' c (B.ST.pprempty (B.ST.rounds c) witness) ((B.init_state c ws rs)) ((B.ST.rounds c)))) = (WC.B.stateful_protocol'' c (WG.G.GT.pprempty (B.ST.rounds c) witness) (WC.B.init_state c ws rs) ((B.ST.rounds c))) ). progress. rewrite -equiv_circ_protocol_stateful_fst' => />*. rewrite /rounds size_ge0 => />*. rewrite /rounds take_size => />*. 
    rewrite B.ST.pmap_eqP => />x H0. rewrite !B.ST.get_pzip3 !H0 => />*.  rewrite equiv_circ_protocol_thr' => />*. rewrite -circ_protocol_take_rs' => />*. qed.

  lemma equiv_circ_protocol c ws rs :
    P.valid_rands c rs =>
      (WC.B.circ_protocol c ws rs) = (WC.B.protocol c ws rs).
    rewrite -WC.B.equiv_stateful_protocol => />*. rewrite equiv_circ_protocol_stateful => />*. qed.

  axiom valid_inputs_cons g c ws r :
    P.valid_inputs (g::c) ws /\ WGP.W.P.valid_rands g r => (WGP.W.P.valid_inputs g ws /\ P.valid_inputs c (WG.G.protocol g ws r).`2).

  lemma valid_inputs_head g c ws :
    P.valid_inputs (g::c) ws => WGP.W.P.valid_inputs g ws.
    pose rs := sample (WGP.W.gen_rand g).
    move => H. have : (WGP.W.P.valid_inputs g ws /\ P.valid_inputs c (WG.G.protocol g ws rs).`2). rewrite valid_inputs_cons => |>i j Hij. rewrite WGP.valid_gen_rand => |>. rewrite /rs sampleE => />. progress. qed. 

  lemma valid_inputs_behead g c ws r :
    P.valid_inputs (g::c) ws /\ WGP.W.P.valid_rands g r => P.valid_inputs c (WG.G.protocol g ws r).`2.
    move => H. have : (WGP.W.P.valid_inputs g ws /\ P.valid_inputs c (WG.G.protocol g ws r).`2). rewrite valid_inputs_cons => />*. progress. qed.

  lemma valid_rands_wg x rs :
    WGP.W.P.valid_rands x rs = WGP.WG.P.valid_rands x rs. progress. qed.

  lemma valid_rands_cons g c rs :
    P.valid_rands (g::c) rs = (P.ST.P.all (fun i r => 0 < List.size r) rs /\ (WGP.W.P.valid_rands g (P.ST.P.map (head witness) rs)) /\ P.valid_rands c (P.ST.P.map behead rs)).
    rewrite !/valid_rands /circ_valid_rands => |>. rewrite eq_logical => |>. rewrite /valid_local_rand => |>. split. rewrite !P.ST.P.allP => />H. split.
    (*forward*)
    move => i Hi1 Hi2. have : B.consistent_rands (cons g c) i i (B.ST.P.get rs i) (B.ST.P.get rs i). rewrite H => />. rewrite /ISet.mem !iset_in_def => />. rewrite /consistent_rands => />H1 H2. rewrite -H1. have : 0 <= size c. rewrite size_ge0 => />. smt(). 
    split. move => i j Hi Hj. have : B.consistent_rands (cons g c) i j (B.ST.P.get rs i) (B.ST.P.get rs j). rewrite H => />. rewrite /consistent_rands => />H2 H3 H4 H5. rewrite !WGP.WG.G.ST.get_pmap => />. have : (fun (g0 : B.G.Gate) (r : B.G.GT.local_rand) => B.G.gate_valid_rand g0 r) g (head witness (B.ST.P.get rs i)). rewrite (lsame_cons_left1 _ g witness c (B.ST.P.get rs i)) => />. have : (fun (g0 : B.G.Gate) (r : B.G.GT.local_rand) => B.G.gate_valid_rand g0 r) g (head witness (B.ST.P.get rs j)). rewrite (lsame_cons_left1 _ g witness c (B.ST.P.get rs j)) => />. simplify. rewrite /gate_valid_rand => />. 
    move => i j Hi Hj. have : B.consistent_rands (cons g c) i j (B.ST.P.get rs i) (B.ST.P.get rs j). rewrite H => />. rewrite /consistent_rands => />H2 H3 H4 H5. rewrite !B.ST.get_pmap => />. rewrite !size_behead => />. rewrite !ge0_max => />. rewrite -H2. have : 0 <= size c. rewrite size_ge0 //. smt(). rewrite -H4. have : 0 <= size c. rewrite size_ge0 //. smt(). rewrite -H2 -H4 => />. rewrite !(lsame_cons_left2 _ g c) => />. 
    (*backward*)
    rewrite P.ST.P.allP => />H H0 H1 i j Hi Hj. have : WGP.WG.G.consistent_rands g i j (WGP.WG.G.ST.P.get (P.ST.P.map (head witness) rs) i) (WGP.WG.G.ST.P.get (P.ST.P.map (head witness) rs) j). rewrite H0 => />. have : B.consistent_rands c i j (B.ST.P.get (P.ST.P.map behead rs) i) (B.ST.P.get (P.ST.P.map behead rs) j). rewrite H1 => />. have : 0 < size (P.ST.P.get rs i). rewrite H => />. move :Hi. rewrite /ISet.mem iset_in_def => />. have : 0 < size (P.ST.P.get rs j). rewrite H => />. move :Hj. rewrite /ISet.mem iset_in_def => />. move => S1 S2. clear H H0 H1. rewrite /consistnet_rands => />. rewrite !B.ST.get_pmap => />. rewrite !size_behead => />. rewrite !ge0_max => />. smt(). smt(). move => H H0 H1 H2 H3 H4. rewrite H => />. rewrite -(head_behead (B.ST.P.get rs i) witness). rewrite -size_nenil => />. rewrite -(head_behead (B.ST.P.get rs j) witness). rewrite -size_nenil => />. rewrite !lsame_cons => />. move :H3 H4. rewrite /gate_valid_rand !WGP.WG.G.ST.get_pmap => />. rewrite !size_behead => />. rewrite !ge0_max => />. smt(). smt(). smt(). qed.

  lemma valid_rands_rcons g c rs :
    P.valid_rands (rcons c g) rs = (P.ST.P.all (fun i r => 0 < List.size r) rs /\ (WGP.W.P.valid_rands g (P.ST.P.map (last witness) rs)) /\ P.valid_rands c (P.ST.P.map nolast rs)).
    rewrite /valid_rands => />. rewrite eq_logical => />. rewrite P.ST.P.allP => />. split.
    (*forward*)
    move => H. split. move => i Hi1 Hi2. have : B.consistent_rands (rcons c g) i i (B.ST.P.get rs i) (B.ST.P.get rs i). rewrite H => />. rewrite /ISet.mem !iset_in_def => />. rewrite /consistent_rands => />. rewrite !size_rcons => />H1. rewrite -H1 => />. have : 0 <= size c. rewrite size_ge0 //. smt().
    split. move => i j Hi Hj. rewrite !WGP.WG.G.ST.get_pmap => />. have : B.consistent_rands (rcons c g) i j (B.ST.P.get rs i) (B.ST.P.get rs j). rewrite H => />. rewrite /consistent_rands => />. rewrite !size_rcons => H1 H2 H3 H4. move :H2 H4. rewrite -(nolast_last (B.ST.P.get rs i) witness). rewrite -size_nenil => />. rewrite -H1 => />. have : 0 <= size c. rewrite size_ge0 //. smt(). rewrite -(nolast_last (B.ST.P.get rs j) witness). rewrite -size_nenil => />. rewrite -H3 => />. have : 0 <= size c. rewrite size_ge0 //. smt(). rewrite !lsame_rcons => />. 
    move => i j Hi Hj. rewrite !B.ST.get_pmap => />. have : B.consistent_rands (rcons c g) i j (B.ST.P.get rs i) (B.ST.P.get rs j). rewrite H => />. clear H. rewrite /consistent_rands !size_nolast => />. rewrite !size_rcons => />H1 H2 H3 H4. rewrite -H1 -H3 => />. rewrite !ge0_max => />. rewrite size_ge0 //. move :H2 H4. rewrite -(nolast_last (B.ST.P.get rs i) witness). rewrite -size_nenil => />. rewrite -H1 => />. have : 0 <= size c. rewrite size_ge0 //. smt(). rewrite -(nolast_last (B.ST.P.get rs j) witness). rewrite -size_nenil => />. rewrite -H3 => />. have : 0 <= size c. rewrite size_ge0 //. smt(). rewrite !lsame_rcons => />. rewrite !nolast_rcons => />. 
    (*backward*)
    move => H H0 H1 i j Hi Hj. rewrite !size_rcons => />. have : WGP.WG.G.consistent_rands g i j (WGP.WG.G.ST.P.get (P.ST.P.map (last witness) rs) i) (WGP.WG.G.ST.P.get (P.ST.P.map (last witness) rs) j). rewrite H0 => />. have : B.consistent_rands c i j (B.ST.P.get (P.ST.P.map nolast rs) i) (B.ST.P.get (P.ST.P.map nolast rs) j). rewrite H1 => />. clear H0 H1. rewrite /consistent_rands !WGP.WG.G.ST.get_pmap => />. rewrite !B.ST.get_pmap => />. rewrite !size_nolast => />. have : 0 < size (P.ST.P.get rs i). rewrite H => />. move :Hi. rewrite /ISet.mem iset_in_def => />. have : 0 < size (P.ST.P.get rs j). rewrite H => />. move :Hj. rewrite /ISet.mem iset_in_def => />. move => H1 H2. rewrite !ge0_max => />. smt(). smt(). move => H3 H4 H5 H6 H7 H8. rewrite H3 => />. rewrite -(nolast_last (B.ST.P.get rs i) witness). rewrite -size_nenil => />. rewrite -(nolast_last (B.ST.P.get rs j) witness). rewrite -size_nenil => />. rewrite !lsame_rcons => />. rewrite !size_rcons => />. rewrite !size_nolast => />. rewrite !ge0_max => />. rewrite -H3 => />. rewrite size_ge0 => />. rewrite -H5 => />. rewrite size_ge0 => />. smt(). qed.

  lemma circ_protocol_thr_rcons' c g ws cs :
    P.valid_rands (rcons c g) cs => 
    (B.circ_protocol' (rcons c g) ws cs).`2.`2 = (WG.G.protocol g (B.circ_protocol' c ws (B.ST.P.map nolast cs)).`2.`2 (B.ST.P.map (last witness) cs)).`2.
    rewrite /WG.G.protocol. rewrite WGP.g_protocol_snd_def => />H.
    move :H. elim:c ws cs => />ws cs H. congr. rewrite (_:B.G.g_protocol=WGP.WG.G.g_protocol). progress. congr. rewrite B.CT.pmap_eqP => />x H0. rewrite !B.CT.get_pmap => />*. move :H. rewrite /valid_rands =>/>H. have : B.consistent_rands (cons g []) x x (B.ST.P.get cs x) (B.ST.P.get cs x). rewrite H => />. rewrite /consistent_rands => />H1 H2. rewrite head_last_eq => />. smt(). 
    move => ws0 cs0 H0. rewrite H => />. move :H0. rewrite valid_rands_cons => />.
    move :H0. rewrite valid_rands_cons valid_rands_rcons !P.ST.P.allP => />H0 H1 H2 H3 H4. 
    rewrite !B.CT.P.map_comp /(\o) => />.
    have : forall x, 0 <= x < P.ST.P.size => 1 < size (B.CT.P.get cs0 x). move => x Hx. have : 0 < size (P.ST.P.get cs0 x). rewrite H0 => />. move => H5. have : 0 < size (P.ST.P.get (P.ST.P.map behead cs0) x). rewrite H2 => />. rewrite P.ST.get_pmap => />. rewrite /ISet.mem iset_in_def => />. move :Hx. progress. rewrite size_behead => />. rewrite ge0_max => />. smt(). smt(). move => H5.
    congr. congr. congr. congr. congr. congr. congr. rewrite B.CT.pmap_eqP => />x Hx. rewrite !B.CT.get_pmap => />. rewrite head_nolast => />. rewrite H5 => />. move :Hx. rewrite /ISet.mem iset_in_def => />.  
    rewrite B.ST.pmap_eqP => />x Hx. rewrite !B.ST.get_pmap => />. rewrite nolast_behead => />. rewrite H5 => />. move :Hx. rewrite /ISet.mem iset_in_def => />. 
    rewrite B.ST.pmap_eqP => />x Hx. rewrite !B.ST.get_pmap => />. rewrite last_behead => />. rewrite H5 => />. move :Hx. rewrite /ISet.mem iset_in_def => />. qed.
    
  lemma circ_protocol_snd_rcons c g ws cs :
    P.valid_rands (rcons c g) cs => 
    (B.circ_protocol (rcons c g) ws cs).`2 = (WG.G.protocol g (B.circ_protocol c ws (B.ST.P.map nolast cs)).`2 (B.ST.P.map (last witness) cs)).`2.
    rewrite /circ_protocol => />*. rewrite circ_protocol_thr_rcons' => />*. qed.

  lemma circ_functionality_cons x l ws :
    circ_functionality (cons x l) ws = circ_functionality l (WG.functionality x ws).
    rewrite /circ_functionality => />*. qed.

  lemma imap_wg_bgt (f:int -> 'a->'b) (xs:'a WG.G.GT.P.arrayN) : 
    WG.G.GT.P.imap f xs = B.G.GT.P.imap f xs. progress. qed.

  lemma circ_functionality_correctness x ws cs :
    P.valid_inputs x ws /\ P.valid_rands x cs =>
      circ_functionality x (unshare_input ws) = unshare_output ((B.circ_protocol x ws cs)).`2.
    move: ws cs. elim x => />x. 
    move => l H ws cs H0 H1. rewrite /unshare_input /unshare_output /circ_funtionality /circ_protocol => />*. 
    have : P.valid_rands (cons x l) cs. rewrite H1 => />*. move => validcs.
    move :H1. rewrite valid_rands_cons => />H2 H3 H4.
    rewrite circ_functionality_cons => />*. rewrite (_: ((WG.functionality x (unshare_input ws))) = (WGP.WG.functionality x ((WGP.WG.unshare_input ws)))). progress. 
    rewrite (_:(WGP.WG.functionality x (WGP.WG.unshare_input ws))=W.functionality x (W.unshare_input ws)). progress. rewrite (WGP.weak_correctness _ _ (P.ST.P.map (head witness) cs)) => />. rewrite (valid_inputs_head x l) => />*. rewrite (H _ (P.ST.P.map behead cs)) => />*. rewrite /valid_local_inputs => />*. rewrite valid_inputs_behead => />*.
    rewrite /unshare /unshare_output /circ_protocol => />*. rewrite /unshare => />*. congr. congr. congr. smt(WGP.g_protocol_def). qed.

  module Rand = {
    proc gen_cons_coins(g:WG.G.Gate,gs) = {
      var c,cs;
      c <$ WG.gen_rand g;
      cs <$ circ_gen_rand gs;
      return (B.CT.pcons c cs);
    }
    proc gen_coins(gs) = {
      var c;
      c <$ circ_gen_rand gs;
      return c;
    }
  }.

  lemma circ_gen_rand_cons g gs :
    circ_gen_rand (g::gs) = dapply (uncurry B.CT.pcons) (WG.gen_rand g `*` circ_gen_rand gs).
    rewrite /circ_gen_rand /circ_gen_rand' => />*. rewrite djoin_cons /uncurry => />*. rewrite !dmap_comp /(\o) => />. rewrite eq_distr => />x. rewrite !dmap1E /(\o) /pred1 => />*. 
    rewrite (_: (fun (x0 : WGP.WG.rand * WGP.WG.rand list) => (B.CT.P.concat (cons x0.`1 x0.`2)) = x) = (fun (x0 : WGP.WG.rand * WGP.WG.rand list) => B.CT.P.merge cons x0.`1 (B.CT.P.concat x0.`2) = x)). rewrite fun_ext=> />*. rewrite B.CT.P.concat_cons => />*. 
    rewrite (_: (fun (x0:_*_) => (B.CT.pcons x0.`1 x0.`2) = x) = (fun (x0:_*_) => (fun x1 => x1 = B.CT.phead x) x0.`1 /\ (fun x2 => (B.CT.P.all (fun _ x => 0 < List.size x) x /\ x2 = B.CT.pbehead x)) x0.`2)). rewrite fun_ext => />*. rewrite B.CT.pcons_eq_l => />*. smt(). rewrite dprodE !dmapE /(\o) => />*. 
    rewrite (_: (fun (x0:_*_) => (B.CT.P.merge (fun x1 xs => cons x1 xs) x0.`1 (B.CT.P.concat x0.`2)) = x) = (fun (x0:_*_) => (fun x1 => x1 = B.CT.phead x) x0.`1 /\ (fun x2 => B.CT.P.all (fun _ x => 0 < List.size x) x /\ B.CT.P.concat x2 = B.CT.pbehead x) x0.`2 ) ). rewrite fun_ext => />*. rewrite B.CT.pcons_eq_l => />*. smt(). rewrite dprodE => />*. qed.

  lemma size_circ_gen_rand_cons g gs xs :
    xs \in circ_gen_rand (g::gs) => B.G.GT.P.all (fun _ x => 0 < List.size x) xs.
    rewrite B.G.GT.P.allP => />H i Hi1 Hi2. rewrite /circ_gen_rand /circ_gen_rand' in H => />*. move :H. rewrite supp_dmap => />a H. move :H. rewrite supp_djoin => />H1 H2. move :H2. rewrite allP => />H2. rewrite size_map in H1 => />*. move :H1 H2. elim a => />H. move: H. elim gs => />. 
    move => l H H1. have : false. have : 0 <= size l. rewrite size_ge0 //. move => H2. smt(). progress. 
    move => l H0 H1 H2. rewrite B.CT.P.concat_cons => />*. rewrite B.G.GT.P.get_merge andabP andaP => />*. have : 0 <= size (B.G.GT.P.get (B.CT.P.concat l) i). rewrite size_ge0 //. smt(). qed.

  clone import ProdSampling as Samp with
    type t1 = WG.rand,
    type t2 = (WG.G.GT.local_rand list) B.G.GT.P.arrayN.

  lemma sample_cons_coins : 
    equiv [ Rand.gen_coins ~ Rand.gen_cons_coins : gs{1}=g{2}::gs{2} ==> ={res} ].
    proc. simplify. 
    alias {1} 1 t = 0. swap{1} 1 1. alias{1} 2 ccs = (B.G.GT.P.map (head witness) c,B.G.GT.P.map behead c).
    alias{2} 2 t = 0. swap{2} 2 1. alias{2} 3 ccs = (c,cs).
    transitivity{1}
      { ccs <@ Samp.S.sample(WG.gen_rand (head witness gs),circ_gen_rand (behead gs)); }
      ( ={gs} /\ 0 < size gs{1} ==> ={ccs} /\ B.G.GT.P.all (fun _ c => 0 < List.size c) c{1} /\ ccs{1}= (B.G.GT.P.map (head witness) c{1},B.G.GT.P.map behead c{1}) )
      ( gs{1}=g{2}::gs{2} ==> ={ccs} /\ ccs{2}=(c{2},cs{2}) ).
      progress. exists (g{2}::gs{2}) => />*. have : 0 <= size gs{2}. rewrite size_ge0 //. smt().
      progress. rewrite B.CT.phead_behead => />*. 
    inline *. wp. sp. rnd (fun c => (B.G.GT.P.map (head witness) c,B.G.GT.P.map behead c)) (fun (c12:_*_) => B.G.GT.pcons c12.`1 c12.`2). auto => />. progress. rewrite B.G.GT.map_head_pcons => />*. rewrite B.G.GT.map_behead_pcons => />*. rewrite -prod_id => />*.
    rewrite -(head_behead gs{2} witness) => />*. rewrite -size_nenil => />*. rewrite circ_gen_rand_cons /uncurry => />*. rewrite dapply1E => />*. rewrite /pred1 /(\o). congr. rewrite fun_ext => />x. rewrite eq2 => />*. rewrite -B.CT.pcons_eq => />*. 
    rewrite supp_dprod => />*. move :H2. rewrite -(head_behead gs{2} witness). rewrite -size_nenil => />*. rewrite circ_gen_rand_cons => />H2. move :H2. rewrite supp_dmap /uncurry => />a Ha. have : a = ((B.G.GT.P.map (head witness) ((B.G.GT.pcons a.`1 a.`2))), (B.G.GT.P.map behead ((B.G.GT.pcons a.`1 a.`2)))). rewrite H0 => />*. rewrite !B.G.GT.map_head_pcons !B.G.GT.map_behead_pcons => />*. rewrite !B.G.GT.map_head_pcons !B.G.GT.map_behead_pcons => />H2. move :H2. rewrite -supp_dprod => />*. rewrite B.G.GT.phead_behead => />*. 

rewrite (size_circ_gen_rand_cons (head witness gs{2}) (behead gs{2}) ) => />*. rewrite (head_behead _ witness) => />*. rewrite -size_nenil => />*. rewrite (size_circ_gen_rand_cons (head witness gs{2}) (behead gs{2}) ) => />*. rewrite (head_behead _ witness) => />*. rewrite -size_nenil => />*. 
    transitivity{2}
      { ccs <@ Samp.S.sample2(WG.gen_rand g,circ_gen_rand gs); }
      ( 0 < size gs{1} /\ gs{1}=g{2}::gs{2} ==> ={ccs} )
      ( ={g,gs} ==> ={ccs} /\ ccs{2} = (c{2}, cs{2}) ); last first.
    inline *. wp. sp. auto => />*. 
      progress. exists (g{2}) (gs{2}) => />*. have : 0 <= size gs{2}. rewrite size_ge0 //. smt(). progress. 
    call sample_sample2 => />*. auto => />*. qed.

  lemma circ_valid_gen_rand x cs :
    cs \in circ_gen_rand x => P.valid_rands x cs.
    rewrite /circ_gen_rand /circ_gen_rand' /circ_valid_rands /circ_valid_rands => />H i j Hij. move :H. rewrite supp_dmap => />a H. 
    rewrite !lsameP => />. rewrite B.CT.P.size_get_concat => />. move :Hij. rewrite /ISet.mem /ISet.iset !iset_in_def => />. 
    move :H. rewrite supp_djoinmap => />H H1. rewrite B.CT.P.size_get_concat => />. move :Hij. rewrite /ISet.mem /ISet.iset !iset_in_def => />. move :H1. rewrite allP => />H1.
    have : (forall i (n : int), ISet.mem i B.ST.partyset => 0 <= n => osame (fun (g : B.G.Gate) (r : B.G.GT.local_rand) => B.G.gate_valid_rand g r) (onth x n) (onth (B.ST.P.get (B.CT.P.concat a) i) n)). 
    move => k n Hk Hn.  
    pose p := (nth witness x n,nth witness a n). case (n < size x) => />Hn1.
    have : p.`2 \in (WG.gen_rand p.`1). rewrite (H1 p) => />*. rewrite /p nth_in_zip => />. move => H2. rewrite !(onth_nth witness) => />. rewrite B.ST.P.size_get_concat => />. move :Hk. rewrite /ISet.mem !iset_in_def => />. rewrite -H => />. rewrite (B.CT.P.nth_get_concat_gt0 witness witness) => />. move :Hk. rewrite /ISet.mem !iset_in_def => />. rewrite -H => />. rewrite -H => />. smt().
    have : W.P.valid_rands p.`1 p.`2. rewrite WGP.valid_gen_rand => />. rewrite /valid_rands => />H5. have : WGP.WG.G.consistent_rands p.`1 k k (WGP.WG.G.ST.P.get p.`2 k) (WGP.WG.G.ST.P.get p.`2 k). rewrite H5 => />. rewrite /consistent_rands => />. 
    rewrite osame_none => />. rewrite !onth_none => />. smt(). rewrite B.ST.P.size_get_concat => />. move :Hk. rewrite /ISet.mem !iset_in_def => />. smt(). move => H2.
    split. move => n Hn. rewrite H2 => />. move :Hij. progress. move => n Hn. rewrite H2 => />. move :Hij. progress. qed.

  abbrev priv_simulator i f yi cs = (circ_simulator' i f yi cs).
  abbrev priv_protocol f ys cs = (WC.B.circ_protocol' f ys cs).
 
  lemma dom_priv_simulator i f yi cs : 
    fdom (priv_simulator i f yi cs).`1 = i /\ fdom (priv_simulator i f yi cs).`2.`1 = i /\ fdom (priv_simulator i f yi cs).`2.`2 = i.
    move :yi cs. elim f => />x. rewrite !fdom_ofset => />. move => l H yi cs. rewrite !fdom_fmerge !fdom_map WGP.dom_simulator_out => />*. 
    pose yi' := (WG.simulator_out i x yi (B.CT.P.map (head witness) cs)).`2.
    pose cs' := (B.CT.P.map behead cs).
    have : fdom (fst3 (circ_simulator' i l yi' cs')) = i /\ fdom (snd3 (circ_simulator' i l yi' cs')) = i /\ fdom (thr3 (circ_simulator' i l yi' cs')) = i. rewrite H => />. progress. rewrite H0 fsetIid => />. rewrite H1 fsetIid => />. qed.

  lemma dom_priv_simulator1 i f yi cs : 
    fdom (priv_simulator i f yi cs).`1 = i.
    have : fdom (priv_simulator i f yi cs).`1 = i /\ fdom (priv_simulator i f yi cs).`2.`1 = i /\ fdom (priv_simulator i f yi cs).`2.`2 = i. rewrite dom_priv_simulator => />*. progress. qed.
  lemma dom_priv_simulator2 i f yi cs : 
    fdom (priv_simulator i f yi cs).`2.`1 = i.
    have : fdom (priv_simulator i f yi cs).`1 = i /\ fdom (priv_simulator i f yi cs).`2.`1 = i /\ fdom (priv_simulator i f yi cs).`2.`2 = i. rewrite dom_priv_simulator => />*. progress. qed.
  lemma dom_priv_simulator3 i f yi cs : 
    fdom (priv_simulator i f yi cs).`2.`2 = i.
    have : fdom (priv_simulator i f yi cs).`1 = i /\ fdom (priv_simulator i f yi cs).`2.`1 = i /\ fdom (priv_simulator i f yi cs).`2.`2 = i. rewrite dom_priv_simulator => />*. progress. qed.

  module Privacy = {
    proc ideal(i,f:WG.G.Gate list,yi) = {
      var cs;
      cs <$ circ_gen_rand' f;
      return (priv_simulator i f yi cs);
    }
    proc real(f:WG.G.Gate list,ys) = {
      var cs;
      cs <$ circ_gen_rand' f;
      return (priv_protocol f ys cs);
    }
  }.

  lemma get_wwgt_wwst (xs:'a B.ST.P.arrayN) i :
    WGP.WG.G.GT.P.get xs i = WGP.WG.G.ST.P.get xs i. progress. qed.

  lemma priv_cons i x l yi ys c1 cs1 c2 cs2 :
    corrupted_set i /\ yi = corrupted i ys /\ WG.P.valid_inputs x ys /\ WG.P.valid_rands x c1 => 
    (WG.simulator_out i x yi c1) = corrupted2 i (WG.G.protocol x ys c2) => 
      priv_simulator i l ((WG.simulator_out i x yi c1).`2) cs1 = corrupted3 i (priv_protocol l (WG.G.protocol x ys c2).`2 cs2) => 
      priv_simulator i (cons x l) yi (B.CT.pcons c1 cs1) = corrupted3 i (priv_protocol (cons x l) ys (B.CT.pcons c2 cs2)).
    rewrite circ_protocol_cons' => />H H0 H1 H2 H3 H4 H5. rewrite -fmap_eqIn => |>*. rewrite /corrupted fdom_fmerge !fdom_ofset !fdom_map => |>*. rewrite WGP.dom_simulator_out => |>*. rewrite dom_priv_simulator1 => |>*. rewrite !fsetIid => |>*. progress.
     have : i0 \in P.ST.partyset. rewrite (in_subset i) => />*. move => ip. 
     rewrite fmerge_some => />*. rewrite fdom_map WGP.dom_simulator_out dom_priv_simulator1 fsetIid => />*. rewrite ofset_some => />*. rewrite /ppcons P.ST.get_ppinit /ISet.mem ip => />*. rewrite /pcons. rewrite P.ST.pmap_eqP => />z Hz. rewrite !P.ST.get_pinit !Hz => />*. rewrite /ppswap => />*. rewrite /get WGP.WG.G.GT.get_ppinit /ISet.mem ip => />*. rewrite WGP.WG.G.GT.get_pinit Hz => />*.
    rewrite (_:((B.CT.P.map (head witness) ((B.CT.P.merge (fun (x1 : B.G.GT.local_rand) (xs : B.G.GT.local_rand list) => cons x1 xs) c1 cs1)))) = c1). rewrite B.CT.pmap_eqP => />w Hw. rewrite B.CT.get_pmap => />. rewrite B.CT.get_pmerge Hw => />*.
    rewrite (_:((B.CT.P.map behead ((B.CT.P.merge (fun (x1 : B.G.GT.local_rand) (xs : B.G.GT.local_rand list) => cons x1 xs) c1 cs1)))) = cs1). rewrite B.CT.pmap_eqP => />w Hw. rewrite B.CT.get_pmap => />*. rewrite B.CT.get_pmerge Hw => />*.
    rewrite (_:((B.ST.P.map (head witness) ((B.CT.P.merge (fun (x1 : B.G.GT.local_rand) (xs : B.G.GT.local_rand list) => cons x1 xs) c2 cs2)))) = c2). rewrite B.CT.pmap_eqP => />w Hw. rewrite B.CT.get_pmap => />*. rewrite B.CT.get_pmerge Hw => />*.
    rewrite (_:((B.ST.P.map behead ((B.CT.P.merge (fun (x1 : B.G.GT.local_rand) (xs : B.G.GT.local_rand list) => cons x1 xs) c2 cs2)))) = cs2). rewrite B.CT.pmap_eqP => />w Hw. rewrite B.CT.get_pmap => />*. rewrite B.CT.get_pmerge Hw => />*. 
    rewrite /simulator_out => />*. rewrite H3 => />*. rewrite !map_some => />*. rewrite /corrupted -mem_fdom fdom_ofset => />*. rewrite WGP.WG.G.GT.get_pmap => />*. rewrite /from_messages => />*. rewrite WGP.WG.G.GT.get_pmap => />*. rewrite /stateful_protocol_round /stateful_local_protocol_round => />*. rewrite WGP.WG.G.GT.get_pimap => />*. rewrite (_:(WG.G.protocol x ys c2)=(WGP.WG.G.protocol x ys c2)). progress. rewrite WGP.g_protocol_def => />*. rewrite /g_protocol => />*. rewrite /corrupted ofset_some => />*. rewrite !P.ST.get_pzip /ISet.mem !ip => />*. rewrite !WGP.WG.G.GT.get_pzip !Hz => />*. rewrite !P.ST.get_pmap => />*. rewrite WGP.WG.G.GT.get_pmap => />*. rewrite get_init => />*. rewrite /get !get_wwgt_wwst (WGP.WG.G.get_send_messages x 0) => />. 
    rewrite /valid_messages WGP.WG.G.ST.P.allP => />k Hk1 Hk2. rewrite WGP.WG.G.ST.get_pimap => />. rewrite /ISet.mem iset_in_def => />. rewrite !WGP.WG.G.ST.get_pzip /ISet.mem !iset_in_def !andaP => />. rewrite WGP.WG.G.valid_local_gate_start => />. 
    rewrite (WGP.WG.G.from_to_local_messages x 0) => />*.
    rewrite /valid_pmsgs WGP.WG.G.ST.P.allP => />k Hk1 Hk2. rewrite WGP.WG.G.ST.P.get_map => />. rewrite WGP.WG.G.ST.P.get_imap => />. rewrite !WGP.WG.G.ST.P.get_zip !andabP !andaP => />. have : WGP.WG.G.valid_local_messages x 0 (WGP.WG.G.local_gate_start k x (WGP.WG.G.ST.P.get ys k) (WGP.WG.G.ST.P.get c2 k)). rewrite WGP.WG.G.valid_local_gate_start => />. move => V1. have : WGP.WG.G.valid_pmsgs x 0 (WGP.WG.G.from_local_messages (WGP.WG.G.local_gate_start k x (WGP.WG.G.ST.P.get ys k) (WGP.WG.G.ST.P.get c2 k))). rewrite WGP.WG.G.valid_pmsgs_from => />. move => V2. rewrite WGP.WG.G.valid_pmsgs_get => />. move :ip. rewrite iset_in_def => />. 
    rewrite WGP.WG.G.ST.get_pmap => />*. rewrite WGP.WG.G.ST.get_pimap => />*. rewrite !WGP.WG.G.ST.get_pmerge !Hz => />*. 
    rewrite (_: (WGP.WG.corrupted_view_outputs i x (AuxSmtMap.ofset (WGP.WG.G.GT.P.get (WGP.WG.G.GT.P.zip3 ys (WGP.WG.G.GT.P.map (fun (bin : WGP.WG.G.local_messages) => WGP.WG.G.GT.P.map (fun (msg : WGP.WG.G.GT.msg) => init 1 (fun (j : int) => if j = 0 then msg else witness))  (WGP.WG.G.from_local_messages bin)) (WGP.WG.G.send_messages (WGP.WG.G.GT.P.imap (fun (i1 : WGP.WG.G.GT.party) (wc : WGP.WG.G.share * WGP.WG.G.GT.local_rand) => WGP.WG.G.local_gate_start i1 x wc.`1 wc.`2) (WGP.WG.G.GT.P.zip ys c2)))) c2)) i)) = corrupted i ((WGP.WG.G.protocol x ys c2)).`2 ). rewrite /corrupted /protocol /corrupted_view_outputs => />*. rewrite -fmap_eqIn => />*. rewrite !fdom_ofset => />i1 Hi1. rewrite !ofset_some /view_output /protocol_end => />*. have : i1 \in P.ST.partyset. rewrite (in_subset i) => />*. progress. rewrite P.ST.get_pimap => />*. rewrite P.ST.get_pzip3 => />*. rewrite /ISet.mem H7 => />*. rewrite /IMap.get /IMap.ofset ofset_some => />*. rewrite !WGP.WG.G.GT.get_pzip3 /ISet.mem !H7 => />*. rewrite WGP.WG.G.GT.get_pmap => />*. rewrite /get /protocol' /protocol'' /rounds iseq_1 => />*. congr. rewrite WGP.WG.G.GT.get_pprset /ISet.mem H7 => />*. rewrite WGP.WG.G.GT.pmap_eqP => />w Hw. rewrite !WGP.WG.G.GT.get_pmap => />*. rewrite WGP.WG.G.GT.get_prset Hw => />*.
    rewrite Array.tP => />*. rewrite /pprempty /ppinit /pinit size_init size_set => />. rewrite WGP.WG.G.GT.get_pinit /ISet.mem H7 => />. rewrite WGP.WG.G.GT.get_pinit Hw => />. rewrite size_init => />u Hu1 Hu2. rewrite get_init andabP andaP => />*. case (u=0) => />. rewrite get_set_eqE => />*. rewrite size_init => />. rewrite /ppswap WGP.WG.G.GT.get_ppinit /ISet.mem H7 /protocol_round => />*. rewrite WGP.WG.G.GT.get_pinit Hw => />*. rewrite WGP.WG.G.GT.get_pimap /local_protocol_round => />*. rewrite !get_wwgt_wwst !(WGP.WG.G.get_send_messages x 0) => />*.
    rewrite /valid_messages WGP.WG.G.ST.P.allP => />k Hk1 Hk2. rewrite WGP.WG.G.ST.get_pimap => />. rewrite /ISet.mem iset_in_def => />. rewrite !WGP.WG.G.ST.get_pzip /ISet.mem !iset_in_def !andaP => />. rewrite WGP.WG.G.valid_local_gate_start => />. 
    rewrite (WGP.WG.G.from_to_local_messages x 0) => />*.
    rewrite /valid_pmsgs WGP.WG.G.ST.P.allP => />k Hk1 Hk2. rewrite WGP.WG.G.ST.P.get_map => />. rewrite WGP.WG.G.ST.P.get_imap => />. rewrite !WGP.WG.G.ST.P.get_zip !andabP !andaP => />. have : WGP.WG.G.valid_local_messages x 0 (WGP.WG.G.local_gate_start k x (WGP.WG.G.ST.P.get ys k) (WGP.WG.G.ST.P.get c2 k)). rewrite WGP.WG.G.valid_local_gate_start => />. move => V1. have : WGP.WG.G.valid_pmsgs x 0 (WGP.WG.G.from_local_messages (WGP.WG.G.local_gate_start k x (WGP.WG.G.ST.P.get ys k) (WGP.WG.G.ST.P.get c2 k))). rewrite WGP.WG.G.valid_pmsgs_from => />. move => V2. rewrite WGP.WG.G.valid_pmsgs_get => />. move :H7. rewrite iset_in_def => />. 
    rewrite WGP.WG.G.ST.get_pmap => />*. rewrite !WGP.WG.G.ST.get_pzip3 !Hw => />*. rewrite WGP.WG.G.ST.get_pimap => />*. rewrite WGP.WG.G.ST.get_pzip Hw /stateful_local_protocol_round => />*. rewrite /get => />*. congr. congr. congr. rewrite /get_local_state /get_local_state' iseq_nil => />*. rewrite /get_local_state /get_local_state' iseq_nil => />*. 
    move => U. rewrite get_set_neqE => />*. have : false. smt(). progress. 
    rewrite -H4 => />*. rewrite (_: (ofmap ((Map.offun (fun (a : WGP.WG.G.GT.party) => if a \in i then Some ((WGP.WG.G.view_output a x (oget ((WGP.WG.simulator i x (corrupted i ys) c1)).[a]))) else None)))) = ((WG.simulator_out i x (corrupted i ys) c1)).`2 ). rewrite /simulator_out /corrupted -fmap_eqIn => />*. 
    rewrite H5 => />*. rewrite /corrupted /protocol => />*. rewrite ofset_some => />*. congr. rewrite /get. congr. congr. congr. rewrite /protocol_end /protocol' => />*. rewrite WGP.WG.G.GT.pmap_eqP => />w Hw. rewrite !WGP.WG.G.GT.get_pimap /local_protocol_end /stateful_local_protocol_end => />*. congr. rewrite !WGP.WG.G.GT.get_pzip3 !Hw => />*. rewrite WGP.WG.G.GT.get_pzip !Hw => />*. rewrite /get_local_state /get_local_state' /rounds iseq_1 => />*. rewrite !WGP.WG.G.GT.get_pzip3 WGP.WG.G.GT.get_pzip !Hw => />*. rewrite /get_local_state /get_local_state' /rounds iseq_1 => />*. rewrite /update_local_state => />*. rewrite !get_wwgt_wwst (WGP.WG.G.get_send_messages x 0) => />*.
    rewrite /valid_messages WGP.WG.G.ST.P.allP => />k Hk1 Hk2. rewrite WGP.WG.G.ST.get_pimap => />. rewrite /ISet.mem iset_in_def => />. rewrite !WGP.WG.G.ST.get_pzip /ISet.mem !iset_in_def !andaP => />. rewrite WGP.WG.G.valid_local_gate_start => />. 
    congr. rewrite WGP.WG.G.ST.P.map_imap_comp /(\o) => />*. rewrite WGP.WG.G.ST.pmap_eqP => />u Hu. rewrite !WGP.WG.G.ST.get_pimap => />*. rewrite WGP.WG.G.ST.get_pzip !Hu /protocol'' iseq_1 => />*. rewrite WGP.WG.G.ST.get_pprset Hw => />*. rewrite WGP.WG.G.ST.get_prget Hu => />*. rewrite WGP.WG.G.ST.get_prset Hu /ppswap => />*. rewrite !WGP.WG.G.ST.get_ppinit Hw => />*. rewrite !WGP.WG.G.ST.get_pinit !Hu => />*. rewrite get_set_eqE /protocol_round /local_protocol_round => />*. rewrite size_init => />. rewrite WGP.WG.G.GT.get_pimap => />*. rewrite !WGP.WG.G.GT.get_pzip3 !Hu /stateful_local_protocol_round => />*. rewrite /get => />*. congr. congr. congr. rewrite /get_local_state /get_local_state' iseq_nil => />*. rewrite /get_local_state /get_local_state' iseq_nil => />*. 
    rewrite !B.ST.map_behead_pcons !B.CT.map_behead_pcons => />*. rewrite !B.ST.map_head_pcons !B.CT.map_head_pcons => />*. rewrite (_:(IMap.ofset (P.ST.P.get ys) i) = corrupted i ys). progress. rewrite H5 => />*. rewrite -fmap_eqIn => />*. rewrite fdom_fmerge !fdom_ofset !fdom_map => />*. rewrite WGP.dom_simulator_out fsetIid => />i0 Hi0. rewrite fmerge_some => />*. rewrite fdom_map /corrupted fdom_ofset => />*. rewrite WGP.dom_simulator_out fsetIid => />*. rewrite !ofset_some => />*. rewrite /pcons P.ST.get_pinit => />*. have : i0 \in P.ST.partyset. rewrite (in_subset i) => />*. progress. rewrite /ISet.mem H6 => />*. rewrite map_some => />*. rewrite -mem_fdom WGP.dom_simulator_out => />*. rewrite /thr3 /simulator_out => />*. rewrite H3 => />*. rewrite (_: WG.G.protocol x ys c2 = WGP.WG.G.protocol x ys c2). progress. rewrite WGP.g_protocol_fst_def => />*. rewrite /corrupted /g_protocol => />*. rewrite ofset_some => />*. rewrite P.ST.get_pzip3 /ISet.mem H6 => />*. 
    rewrite (_:(IMap.ofset (P.ST.P.get ys) i) = corrupted i ys). progress. rewrite !B.CT.map_head_pcons !B.CT.map_behead_pcons. rewrite H5 => />*. rewrite !B.ST.map_head_pcons !B.ST.map_behead_pcons. rewrite /corrupted => />*. qed.

  lemma circ_privacy (F:WC.B.Circuit) (I:WC.B.ST.party fset) :
    equiv [Privacy.ideal ~ Privacy.real : corrupted_set I /\ P.valid_inputs f{2} ys{2} /\ i{1}=I /\ f{1} = F /\ yi{1} = corrupted I ys{2} /\ ={f} ==> res{1} = corrupted3 I res{2} ].
    elim F.
    (*Nil*)
    proc. inline *. simplify. auto => />. progress.
    rewrite /corrupted -fmap_eqIn => />. rewrite !fdom_ofset => />i Hi. rewrite !ofset_some => />*. rewrite P.ST.get_ppinit /ISet.mem => />*. have : i \in P.ST.partyset. rewrite (in_subset I) => />*. move => Hi'. rewrite Hi' => />*. rewrite -fmap_eqIn => />*. rewrite !fdom_ofset => />i Hi. rewrite !ofset_some => />*. rewrite P.ST.get_pinit /ISet.mem => />*. have : i \in P.ST.partyset. rewrite (in_subset I) => />*. move => Hi'. rewrite Hi' => />*. rewrite /fredom -fmap_eqIn => />. rewrite !fdom_ofset => />i Hi. rewrite !ofset_some /get /corrupted => />*. rewrite !ofset_some => />*. 
    (*Cons*) 
    move => x l R. proc. wp. sp. simplify. 
    (*Change left randomness*)
    transitivity{1}
      { cs <@ Rand.gen_cons_coins(x,l); }
      ( ={i,f,yi} /\ i{1}=I /\ f{1}=x::l ==> ={i,f,yi,cs} /\ i{1}=I /\ f{1}=x::l )
      ( ={f} /\ corrupted_set I /\ P.valid_inputs f{2} ys{2} /\ f{1}=x::l /\ i{1}=I /\ yi{1}=corrupted I ys{2} ==> ={f} /\ f{1}=x::l /\ i{1}=I /\ yi{1}=corrupted I ys{2} /\ priv_simulator i{1} f{1} yi{1} cs{1} = corrupted3 I (priv_protocol f{2} ys{2} cs{2})  ).
      progress. exists (x::l) (i{1}) (corrupted i{1} ys{2}) => />*.
      progress. 
    transitivity{1}
      { cs <@ Rand.gen_coins(f); }
      ( ={i,f,yi} /\ i{1}=I /\ f{1}=x::l ==> ={i,f,yi,cs} /\ i{1}=I /\ f{1}=x::l )
      ( ={i,f,yi} /\ i{1}=I /\ f{1}=x::l ==> ={i,f,yi,cs} /\ i{1}=I /\ f{1}=x::l ).
      progress. exists (x::l) (i{2}) (yi{2}) => />*.
      progress. 
    inline *. wp. sp. auto => />*. 
    call sample_cons_coins => />*. auto => />*.
    (*Change right randomness*)
    transitivity{2}
      { cs <@ Rand.gen_cons_coins(x,l); }
      ( ={f} /\ corrupted_set I /\ P.valid_inputs f{2} ys{2} /\ f{1}=x::l /\ i{1}=I /\ yi{1}=corrupted I ys{2} ==> ={f} /\ f{1}=x::l /\ i{1}=I /\ yi{1}=corrupted I ys{2} /\ priv_simulator i{1} f{1} yi{1} cs{1} = corrupted3 I (priv_protocol f{2} ys{2} cs{2}) )
      ( ={f,ys} /\ f{1}=x::l ==> ={f,ys,cs} /\ f{1}=x::l ); last first.
    transitivity{2}
      { cs <@ Rand.gen_coins(f); }
      ( ={f,ys} /\ f{1}=x::l ==> ={f,ys,cs} /\ f{1}=x::l )
      ( ={f,ys} /\ f{1}=x::l ==> ={f,ys,cs} /\ f{1}=x::l ); last first.
    inline *. wp. sp. auto => />*.
      progress. exists (x::l) (ys{2}) => />*.
      progress.
    symmetry. call sample_cons_coins => />*. auto => />*.
      progress. exists (x::l) (ys{2}) => />*.
      progress.
    (*start inductive proof*)
    inline *. wp. sp. simplify. 
    alias{1} 2 sivig = WG.simulator_out i x yi c. 
    alias{2} 2 svg = WG.G.protocol x ys c.
    seq 2 2 : ( ={f,g,gs} /\ corrupted_set I /\ P.valid_inputs f{2} ys{2} /\ i{1}=I /\ f{1}=x::l /\ sivig{1} = corrupted2 I svg{2} /\ sivig{1}=WG.simulator_out I x yi{1} c{1} /\ svg{2}=WG.G.protocol x ys{2} c{2} /\ g{1}=x /\ gs{1}=l /\ yi{1}=corrupted I ys{2} /\ WG.P.valid_rands g{1} c{1} /\ WG.P.valid_rands g{2} c{2} /\ P.valid_inputs gs{2} svg{2}.`2 ). 
    (*Gate*)
    (*cosmetic ideal*)
    transitivity{1}
      { sivig <@ WGP.WeakPrivacy.ideal_out'(I,x,yi) ; }
      ( ={g,gs,f,i,yi} /\ f{1}=x::l /\ g{2}=x /\ gs{2}=l /\ i{1}=I ==> ={g,gs,f,i,yi,sivig} /\ g{1}=x /\ gs{1}=l /\ i{1}=I /\ sivig{1}=WG.simulator_out I x yi{1} c{1} /\ WG.P.valid_rands g{1} c{1} )
      ( ={g,gs,f} /\ corrupted_set I /\ P.valid_inputs f{2} ys{2} /\ f{1}=x::l /\ i{1}=I /\ g{2}=x /\ gs{2}=l /\ yi{1}=corrupted I ys{2} ==> ={g,gs,f} /\ g{1}=x /\ gs{1}=l /\ i{1}=I /\ f{1}=x::l /\ yi{1}=corrupted I ys{2} /\ sivig{1} = corrupted2 I svg{2} /\ svg{2}=WG.G.protocol x ys{2} c{2} /\ corrupted_set I /\ P.valid_inputs f{2} ys{2} /\ WG.P.valid_rands g{2} c{2} /\ P.valid_inputs gs{2} svg{2}.`2 ).
      progress. exists (g{2}::gs{2}) (g{2}) (gs{2}) (i{1}) (corrupted i{1} ys{2}) => />*.
      progress.
    inline *. wp. sp. conseq (_ : _ ==> c{1}=cs1{2} /\ WG.P.valid_rands g{1} c{1}). progress. clear R. auto => />. progress. have : W.P.valid_rands x cL. rewrite (WGP.valid_gen_rand x) => />*. rewrite /valid_rands => />*. 
    (*cosmetic real*)
    transitivity{2}
      { svg <@ WGP.WeakPrivacy.real_out'(x,ys); }
      ( ={g,gs,f} /\ corrupted_set I /\ P.valid_inputs f{2} ys{2} /\ f{1}=x::l /\ i{1}=I /\ g{2}=x /\ gs{2}=l /\ yi{1}=corrupted I ys{2} ==> ={g,gs,f} /\ g{1}=x /\ gs{1}=l /\ i{1}=I /\ f{1}=x::l /\ yi{1}=corrupted I ys{2} /\ sivig{1} = corrupted2 I svg{2} /\ corrupted_set I /\ P.valid_inputs f{2} ys{2} )
      ( ={g,gs,f,ys} /\ f{1}=x::l /\ g{2}=x /\ gs{2}=l /\ P.valid_inputs f{2} ys{2} ==> ={g,gs,f,ys,svg} /\ g{1}=x /\ gs{1}=l /\ svg{2}=WG.G.protocol x ys{2} c{2} /\ WG.P.valid_rands g{2} c{2} /\ P.valid_inputs gs{2} svg{2}.`2 ); last first.
    inline *. wp. sp. conseq (_ : _ ==> cs1{1}=c{2} /\ WG.P.valid_rands g{2} c{2}). progress.  smt(valid_inputs_behead). 
    clear R. auto => />. progress. have : W.P.valid_rands x cs1L. rewrite (WGP.valid_gen_rand x) => />. rewrite /valid_rands => />*.
      progress. exists (g{2}::gs{2}) (g{2}) (gs{2}) (ys{2}) => />*. 
      progress. 
    (*G privacy*)
    call (WGP.weak_privacy_out' I) => />*. clear R. auto => />. progress. smt(valid_inputs_head). 
    (*tie inductive argument*)
    alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 sivi = priv_simulator I l sivig.`2 cs0.
    alias{2} 1 t = 0. swap{2} 1 1. alias{2} 2 sv = priv_protocol l svg.`2 cs0.
    (*cosmetic ideal*)
    transitivity{1}
      { sivi <@ Privacy.ideal(I,l,sivig.`2); }
      ( ={g,gs,f,yi,i,sivig} /\ WG.P.valid_rands g{1} c{1} /\ corrupted_set I /\ g{1}=x /\ gs{1}=l /\ f{1}=x::l /\ i{1}=I /\ sivig{1} = (WG.simulator_out I x yi{1} c{1}) ==> ={i,g,gs,f,yi,sivi,sivig} /\ WG.P.valid_rands g{1} c{1} /\ f{1}=x::l /\ g{1}=x /\ sivig{1} = (WG.simulator_out I x yi{1} c{1}) /\ sivi{1}=priv_simulator I l sivig{1}.`2 cs0{1} /\ corrupted_set I  )
      ( ={g,gs,f} /\ corrupted_set I /\ P.valid_inputs gs{2} svg{2}.`2 /\ WG.P.valid_rands g{2} c{2} /\ P.valid_inputs f{2} ys{2} /\ g{1}=x /\ gs{1}=l /\ f{1}=x::l /\ i{1}=I /\ yi{1}=corrupted I ys{2} /\ svg{2} = (WG.G.protocol x ys{2} c{2}) /\ sivig{1} = corrupted2 I svg{2} ==> ={g,gs,f} /\ P.valid_inputs gs{2} svg{2}.`2 /\ WG.P.valid_rands g{2} c{2} /\ f{1}=x::l /\ i{1}=I /\ g{1}=x /\ yi{1}=corrupted I ys{2} /\ sv{2}=priv_protocol l (svg{2}.`2) cs0{2} /\ sivi{1} = corrupted3 I sv{2} /\ svg{2} = (WG.G.protocol x ys{2} c{2}) /\ sivig{1} = corrupted2 I svg{2} /\ P.valid_inputs f{2} ys{2} /\ P.valid_rands gs{2} cs0{2} ).
      progress. exists (g{2}::gs{2}) (g{2}) (gs{2}) (i{1}) (corrupted2 i{1} (WG.G.protocol g{2} ys{2} c{2})) (corrupted i{1} ys{2}) => />*. 
      move => &1 &m &2 H H0. have : f{1} = cons x l. move :H. progress. move => f1. have : f{2} = cons x l. move :H H0. progress. move => f2. rewrite !f1 !f2. rewrite (priv_cons i{1} x l yi{1} ys{2} c{1} cs0{1} c{2} cs0{2}) => |>. move :H H0. progress. move :H H0. progress. move :H H0. progress. move :H0. rewrite /corrupted_set => |>. rewrite /corrupted_set => |>. rewrite (_:(WG.P.valid_inputs g{2} ys{2})=(WGP.W.P.valid_inputs g{2} ys{2})). progress. rewrite (valid_inputs_head g{2} l ys{2}) => |>. move :H0 H. progress. move :H H0. rewrite /corrupted_set => />H H0. move :H H0. progress. rewrite -H4 => |>. move :H H0. progress. move :H H0. progress. 
    inline *. wp. sp. conseq (_:_ ==> cs0{1}=cs1{2}) => />*. auto => />*.
    (*cosmetic real*)
    transitivity{2}
      { sv <@Privacy.real(l,svg.`2); }
      ( ={g,gs,f} /\ P.valid_inputs gs{2} svg{2}.`2 /\ corrupted_set I /\ i{1}=I /\ yi{1} = corrupted i{1} ys{2} /\ g{1}=x /\ gs{1}=l /\ f{1}=x::l /\ sivig{1} = corrupted2 I svg{2} ==> ={g,gs,f} /\ corrupted_set I /\ P.valid_inputs gs{2} svg{2}.`2 /\ yi{1} = corrupted i{1} ys{2} /\ i{1}=I /\ g{1}=x /\ gs{1}=l /\ f{1}=x::l /\ sivig{1} = corrupted2 I svg{2} /\ sivi{1} = corrupted3 I sv{2} /\ P.valid_inputs gs{2} svg{2}.`2 )
      ( ={g,gs,f,ys,svg} /\ P.valid_inputs gs{2} svg{2}.`2 /\ P.valid_inputs f{2} ys{2} /\ g{2}=x /\ gs{2}=l /\ svg{2} = (WG.G.protocol x ys{2} c{2}) /\ WG.P.valid_rands g{2} c{2} ==> ={g,gs,f,ys,svg,sv} /\ g{2}=x /\ gs{2}=l /\ svg{2} = (WG.G.protocol x ys{2} c{2}) /\ sv{2}=priv_protocol l (svg{2}.`2) cs0{2} /\ P.valid_inputs f{2} ys{2} /\ WG.P.valid_rands g{2} c{2} /\ P.valid_inputs gs{2} svg{2}.`2 /\ P.valid_rands gs{2} cs0{2} ); last first.
    inline *. wp. sp. conseq (_:_ ==> cs1{1}=cs0{2} /\ P.valid_rands gs{2} cs0{2}) => />*. clear R. auto => />. progress. rewrite (circ_valid_gen_rand l) => />*.
      progress. exists (g{2}::gs{2}) (g{2}) (gs{2}) (WG.G.protocol g{2} ys{2} c{2}) ys{2} => />*.  
      progress.  
    call R => />*. clear R. auto => />*.  
    qed.
    
  clone include WeakProofs with
    theory W = WC
    proof *.
    realize gen_rand_ll.
    rewrite /gen_rand /circ_gen_rand /circ_gen_rand' /(\o) => />p. elim p => />.
    rewrite !dmap_ll djoin_ll => />.
    move => x l H.
    rewrite djoin_cons. rewrite !dmap_ll dprod_ll. rewrite !ll_dmap in H. rewrite H. 
    rewrite WGP.gen_rand_ll => />*. qed.
    realize valid_gen_rand.
    progress. have : P.valid_rands x rs. rewrite circ_valid_gen_rand => />*. progress. qed.
    realize weak_correctness.
    rewrite /functionality => />x ys cs H H0. 
    rewrite (circ_functionality_correctness x _ cs) => />*. rewrite /unshare_output equiv_circ_protocol => />*. qed.
    realize dom_simulator.
    rewrite /simulator /circ_simulator /circ_simulator_sz => />i x ws r. rewrite !fdom_fredom => />. qed.
    realize weak_privacy.
    exists* (i{1}). exists* (p{1}). elim*.
    progress. proc. sp. simplify. 
    alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 sivi = priv_simulator f0 p yi cs.
    alias{2} 1 t = 0. swap{2} 1 1. alias{2} 2 sv = priv_protocol p ys cs.
    transitivity{1}
      { sivi <@ Privacy.ideal(f0,p,yi); }
      ( ={i,p,ys,yi} /\ corrupted_set i{1} /\ p{1}=f /\ i{1}=f0 /\ yi{1} = corrupted f0 ys{1} ==> ={i,p,ys,sivi,yi} /\ corrupted_set i{1} /\ p{1}=f /\ i{1}=f0 /\ yi{1} = corrupted f0 ys{1} /\ sivi{1}=priv_simulator f0 p{1} yi{1} cs{1} )
      ( ={i,p,ys} /\ corrupted_set i{1} /\ W.P.valid_inputs p{1} ys{1} /\ p{1}=f /\ i{1}=f0 /\ yi{1} = corrupted f0 ys{1} ==> i{1}=f0 /\ corrupted_set i{1} /\ W.P.valid_inputs p{1} ys{1} /\ ={i,p,ys} /\ p{1}=f /\ sv{2}=priv_protocol p{2} ys{2} cs{2} /\ sivi{1} = corrupted3 f0 sv{2} /\ P.valid_rands p{2} cs{2} ).
      progress. exists (i{2}) (p{2}) (corrupted i{2} ys{2}) (ys{2}) => |>*. 
      progress. rewrite /simulator /circ_simulator /circ_simulator_sz => |>*. rewrite H2 => |>. rewrite /corrupted => |>*. rewrite -fmap_eqIn => |>*. rewrite /redom !fdom_ofset => |>j Hj. rewrite /get !ofset_some => |>*. rewrite !fzip_some => |>. rewrite !fdom_ofset !fdom_fzip !fdom_map !fdom_ofset !fsetIid => |>*. rewrite !fdom_map !fdom_ofset fsetIid => |>. rewrite !ofset_some => |>*. rewrite !map_some => |>*. rewrite -mem_fdom fdom_ofset => |>*. rewrite !ofset_some => |>*. rewrite !eq2 => |>. rewrite (_:W.P.protocol=B.protocol). progress. rewrite -!equiv_circ_protocol => |>. rewrite /circ_protocol => />*. rewrite WGP.WG.G.GT.get_pzip3 /ISet.mem => />*. have : j \in B.CT.partyset. move :H. rewrite /corrupted_set /ISet.subset => />H4 H5. rewrite (in_subset i{2}) => />*. progress. rewrite !H4 => />*. rewrite !H4 => |>. rewrite WGP.WG.G.GT.get_pmap /ISet.mem => />*. rewrite H4 => />*. 
    inline *. wp. sp. auto => />*.  
    transitivity{2}
      { sv <@ Privacy.real(p,ys); }
      ( ={i,p,ys} /\ corrupted_set i{1} /\ W.P.valid_inputs p{1} ys{1} /\ i{1}=f0 /\ p{1}=f /\ yi{1} = corrupted f0 ys{2} ==> ={i,p,ys} /\ corrupted_set i{1} /\ W.P.valid_inputs p{1} ys{1} /\ p{1}=f /\ i{1}=f0 /\ sivi{1} = corrupted3 f0 sv{2} )
      ( ={i,p,ys} /\ corrupted_set i{1} /\ W.P.valid_inputs p{1} ys{1} /\ i{1}=f0 /\ p{1}=f ==> ={i,p,ys,sv} /\ corrupted_set i{1} /\ i{1}=f0 /\ p{1}=f /\ sv{2}=priv_protocol p{2} ys{2} cs{2} /\ W.P.valid_inputs p{1} ys{1} /\ P.valid_rands p{2} cs{2}); last first.
    inline *. wp. sp. auto => />. progress. rewrite circ_valid_gen_rand => />*.
      progress. exists (i{2}) (p{2}) (ys{2}) => />*. 
      progress. 
    call (circ_privacy f f0) => />*. auto => />*. qed. 

end WeakCircuitProofs.
