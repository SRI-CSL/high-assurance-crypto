require import AllCore Int List FSet SmtMap.
require import Aux AuxList AuxFSet AuxSmtMap NextMsgTrace NextMsgArray.
require import NextMsgISet NextMsgIMap.

import ISet IMap Array.

theory Protocol.

  clone import Trace as T.
  import P.

  (* Local Protocol *)

  (* Abstract operator to define *)
  op local_protocol_round : party -> round -> public_input -> local_input -> local_rand -> in_msgs -> pmsgs.

  (* Abstract operator to define *)
  op local_protocol_end : party -> public_input -> local_input -> local_rand -> in_msgs -> local_output.

  (* assumes that local view has already been completely computed *)
  op local_protocol'' (i:party) (x:public_input) wi ri ins sz (rounds:round) : out_msgs =
    foldl (fun (outs:out_msgs) (round:int) => prset outs round (local_protocol_round i round x wi ri ins)) (prempty sz witness) (iseq rounds).

  op local_protocol' (i:party) (x:public_input) (vi:view) : out_msgs =
    local_protocol'' i x vi.`1 vi.`2.`2 vi.`2.`1 (rounds x) (rounds x).

  op local_protocol (i:party) (x:public_input) (vi:view) : out_msgs * local_output =
    let outs = local_protocol' i x vi in
    let out = local_protocol_end i x vi.`1 vi.`2.`2 vi.`2.`1 in
    (outs,out).

  (* Abstract axiom to prove *)
  (* protocol execution shall ignore future messages *)
  axiom local_protocol_round_prefix i n x ws rs ins1 ins2 :
    (forall r, 0 <= r < n => prget ins1 r = prget ins2 r) =>
    ISet.mem i partyset /\ 0 <= n => 
      local_protocol_round i n x ws rs ins1 = local_protocol_round i n x ws rs ins2. 

  lemma local_protocol_round_prmsgs_up_to sz i n n2 x ws rs ins :
    (forall i, ISet.mem i partyset => Array.size (P.get ins i) = sz) =>
    ISet.mem i partyset /\ 0 <= n /\ n <= n2 /\ n < sz /\ n2 <= sz => 
      local_protocol_round i n x ws rs ins = local_protocol_round i n x ws rs (prmsgs_up_to n2 ins).
    move => H H0. rewrite (local_protocol_round_prefix _ _ _ _ _ ins (prmsgs_up_to n2 ins)) => |>. move => r Hr1 Hr2. rewrite /prget /prmsgs_up_to => |>. rewrite pmap_eqP => |>k Hk. rewrite !get_pinit !Hk => |>. rewrite /prfilter get_map => |>. move :Hk. rewrite /ISet.mem iset_in_def => |>. rewrite /filter get_init => |>. rewrite H => |>. have : 0 <= r < sz. smt(). move => H1. rewrite H1 => |>. rewrite /ISet.mem iset_in_def Hr1 => |>. have : r < n2. smt(). move => H2. rewrite H2 => |>. smt(). qed.

  lemma size_get_local_protocol'' i x ws rs ins sz n j :
    0 <= j /\ j < P.size => 0 <= sz =>
    Array.size ((P.get (local_protocol'' i x ws rs ins sz n) j)) = sz.
    rewrite /local_protocol''. elim/natind:n => |>n H1 H2 H3 H4.
    rewrite iseq_nil => |>. rewrite /prempty /pinit P.get_init andabP andaP => |>. rewrite /empty Array.size_init => |>. rewrite ge0_max => |>.
    move => H5. rewrite iseq_succ => |>. rewrite foldl_rcons => |>. rewrite get_prset => |>. rewrite /ISet.mem iset_in_def andaP => |>. rewrite Array.size_set => |>. rewrite H2 => |>. qed.

  lemma size_get_local_protocol' i x vi j :
    0 <= j < P.size => 
    Array.size ((P.get (local_protocol' i x vi) j)) = rounds x.
    rewrite /local_protocol' => |>H1 H2. rewrite size_get_local_protocol'' => |>. rewrite rounds_ge0 => |>. qed.

  lemma local_protocol_round_set sz i n x ws rs ins m :
    rounds x <= sz =>
    ISet.mem i partyset /\ prdom sz n ins /\ 0 <= n /\ n < rounds x =>
      local_protocol_round i n x ws rs (prset ins n m) = local_protocol_round i n x ws rs ins.
   move => |>H0 H1 H2 H3 H4. rewrite (local_protocol_round_prmsgs_up_to sz _ _ n) => |>.
   move => k1 H6. rewrite get_prset H6 => |>. rewrite Array.size_set => |>. move :H2. rewrite /prdom P.allP => |>H2. have : rdom sz n ((P.get ins k1)). rewrite H2 => |>. move :H6. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. smt(). 
   rewrite prmsgs_up_to_lt_set => |>*. rewrite -(local_protocol_round_prmsgs_up_to sz _ _ n) => |>.
   move => k Hk. move :H2. rewrite /prdom P.allP => |>H2. have : rdom sz n ((P.get ins k)). rewrite H2 => |>. move :Hk. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. smt(). qed.

  lemma local_protocol_prmsgs_up_to'' sz i x wi ri ins (rounds1 rounds2 rounds3:round) :
    rounds x <= sz =>
    ISet.mem i partyset => prdom sz rounds3 ins /\ rounds1 <= rounds2 /\ rounds2 <= rounds3 /\ rounds3 <= rounds x =>
      local_protocol'' i x wi ri ins sz rounds1 = local_protocol'' i x wi ri (prmsgs_up_to rounds2 ins) sz rounds1.
    rewrite /local_protocol'' => |>H1 H2 H3 H4 H5 H6. move :H4. elim/natind: rounds1 => |>n N1 N2. rewrite !iseq_nil => |>*.
    rewrite !iseq_succ => |>N3. rewrite !foldl_rcons => |>*. rewrite !N2 => |>*. smt(). congr. rewrite (local_protocol_round_prmsgs_up_to sz i n rounds2 x wi ri (prmsgs_up_to rounds2 ins)) => |>. move => k N4.
    rewrite /prmsgs_up_to /prfilter get_pmap => |>. rewrite Array.size_init => |>. rewrite ge0_max => |>. rewrite Array.size_ge0 => |>. move :H3. rewrite /prdom P.allP => |>H3. have : rdom sz rounds3 ((P.get ins k)). rewrite H3 => |>. move :N4. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. smt().
    rewrite prmsgs_up_to_lt. smt(). rewrite - (local_protocol_round_prmsgs_up_to sz _ n rounds2) => |>. move => k Hk. move :H3. rewrite /prdom P.allP => |>H3. have : rdom sz rounds3 ((P.get ins k)). rewrite H3 => |>. move :Hk. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. smt(). qed.

  lemma local_protocol_set'' sz i x wi ri ins outs (rounds2 n : round) :
    rounds x <= sz =>
    0 <= sz => (ISet.mem i partyset /\ prdom sz n ins /\ 0 <= rounds2 /\ rounds2 <= n /\ n < rounds x) =>
      local_protocol'' i x wi ri (prset ins n outs) sz rounds2 = local_protocol'' i x wi ri ins sz rounds2.
    move => |> H H0 H1 H2 H3 H4 H5. rewrite (local_protocol_prmsgs_up_to'' sz _ _ _ _ _ rounds2 rounds2 (n+1)) => |>. 
    rewrite prdom_prset => |>*. smt(). smt(). rewrite prmsgs_up_to_lt_set => |>*. rewrite - (local_protocol_prmsgs_up_to'' sz _ _ _ _ _ rounds2 rounds2 n) => |>*. smt(). qed.

  lemma local_protocol_succ'' i x wi ri ins sz n :
    0 <= n => local_protocol'' i x wi ri ins sz (n+1) = prset (local_protocol'' i x wi ri ins sz n) n (local_protocol_round i n x wi ri ins).
    rewrite /local_protocol'' => |>*. rewrite iseq_succ => |>*. rewrite foldl_rcons => |>*. qed.

  lemma prdom_local_protocol'' i x wi ri ins sz r :
    0 <= sz => ISet.mem i partyset /\ prdom sz r ins /\ 0 <= r /\ r <= rounds x =>
      prdom sz r (local_protocol'' i x wi ri ins sz r).
    rewrite /local_protocol''. move:ins. elim/natind:r => |>n H. move => ins H2 H3 H4 H5 H6. rewrite iseq_nil => |>. rewrite prdom_prempty. progress. progress. 
    move => H2 ins H3 H4 H5 H6 H7. rewrite iseq_succ => |>. rewrite foldl_rcons => |>. rewrite prdom_prset. progress. progress.
    rewrite (prdom_foldl_prset sz (fun r => local_protocol_round i r x wi ri ins) _ n) => |>*. qed.

  lemma prdom_local_protocol' i x (v:view) :
    ISet.mem i partyset /\ prdom (rounds x) (rounds x) v.`2.`1 =>
      prdom (rounds x) (rounds x) (local_protocol' i x v).
    rewrite /local_protocol' => |>*. rewrite prdom_local_protocol'' => |>*. rewrite rounds_ge0 => |>*. rewrite rounds_ge0 => |>. qed.

  lemma get_local_protocol_prefix'' i x wi ri ins sz1 sz2 r j n :
    ISet.mem i partyset => ISet.mem j partyset =>
    0 <= n => n < r => r <= sz1 => r <= sz2 =>
    get (P.get (local_protocol'' i x wi ri ins sz1 r) j) n =
    get (P.get (local_protocol'' i x wi ri ins sz2 r) j) n.
    move => Hi Hj H. elim/natind:r => |>r.
    move => Hr1 Hr2 Hr3 Hr4. rewrite /local_protocol'' !iseq_nil => |>. rewrite !get_prempty !Hj => |>. rewrite !get_init => |>.
    move => Hr1 R Hr2 Hr3 Hr4. rewrite !local_protocol_succ'' => |>. rewrite !get_prset !Hj => |>. case (n=r) => |>.
    rewrite !get_set_eqE => |>. rewrite size_get_local_protocol'' => |>. move :Hj. rewrite /ISet.mem iset_in_def => |>. smt(). smt(). rewrite size_get_local_protocol'' => |>. move :Hj. rewrite /ISet.mem iset_in_def => |>. smt(). smt().
    move => Hnr. rewrite !get_set_neqE => |>. rewrite R => |>. smt(). smt(). smt(). qed.

  lemma local_protocol_get_get'' sz i n x ws rs ins j :
    rounds x <= sz =>
    (ISet.mem i partyset /\ ISet.mem j partyset /\ 0 <= n /\ n < rounds x /\ ISet.subset (ISet.iset (rounds x)) (roundset x) /\ prdom sz (rounds x) ins) => 
      P.get (local_protocol_round i n x ws rs ins) j = Array.get (P.get (local_protocol'' i x ws rs ins sz (rounds x)) j) n.
    pose r := rounds x. move => |> H H0 H1 H2 H3 H4 H5. have : rounds x <= sz. rewrite H => |>. rewrite /r in H5. move : H H0 H1 H2 H3 H4 H5.
    elim/natind: r ins => |>. move => |> n0 H10 H1 ins H2 H3 H4 H5 H6 H7 H8. rewrite /local_protocol'' iseq_nil => |>*. smt(). 
    move => |> n0 H H0 ins H8 H1 H2 H3 H4 H5 H6 H7. rewrite local_protocol_succ'' => |>. rewrite get_prset H2 => |>.
    case (n=n0) => |>. rewrite Array.get_set_eqE => |>H10. rewrite size_get_local_protocol'' => |>. move :H2. rewrite /ISet.mem iset_in_def => |>. smt(). smt().
    move => H10. rewrite Array.get_set_neqE => |>*. rewrite (local_protocol_prmsgs_up_to'' sz i x ws rs ins n0 n0 (rounds x)) => |>. 
    move :H5. rewrite /ISet.subset => />S. have : (ISet.mem n0 (roundset x)). move :S. rewrite /subset subsetP /(<=) => />S. rewrite /ISet.mem S => |>. rewrite /ISet.iset iset_in_def => |>. smt(). rewrite /ISet.mem iset_in_def => |>. smt().
    rewrite -H0 => |>. smt(). smt(). rewrite /ISet.subset /ISet.iset. rewrite (AuxFSet.subset_trans _ ((AuxFSet.iset (n0 + 1))) _) => |>. rewrite AuxFSet.le_subset_iset => />. smt(). 
    rewrite prdom_prmsgs_up_to => |>. move => k Hk. move :H6. rewrite /prdom P.allP => |>H11. have : rdom sz (rounds x) ((P.get ins k)). rewrite H11 => |>. move :Hk. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. 
    move :H5. rewrite /ISet.subset subsetP /(<=) => |>H5. have : (n0 \in (roundset x)). rewrite H5 => |>. rewrite /ISet.iset iset_in_def => |>. smt(). rewrite /roundset /ISet.iset iset_in_def => |>. smt(). 
    rewrite -(local_protocol_round_prmsgs_up_to sz _ n n0) => |>. move => k Hk. move :H6. rewrite /prdom P.allP => |>H11. have : rdom sz (rounds x) ((P.get ins k)). rewrite H11 => |>. move :Hk. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. 
    move :H5. rewrite /ISet.subset subsetP /(<=) => |>H5. have : (n0 \in (roundset x)). rewrite H5 => |>. rewrite /ISet.iset iset_in_def => |>. smt(). rewrite /roundset /ISet.iset iset_in_def => |>. smt(). qed.

  lemma local_protocol_prget'' x ws ins rs i n :
    (ISet.mem i partyset /\ ISet.mem n (roundset x) /\ prdom (rounds x) (rounds x) ins) => 
      local_protocol_round i n x ws rs ins = prget (local_protocol' i x (ws,(ins,rs))) n.
    move => |>H H0 H1. rewrite /prget /local_protocol' /fopt => |>. rewrite pmap_eqP => |>. move => |> j Hj. rewrite get_pinit => |>*. rewrite Hj => |>*. rewrite (local_protocol_get_get'' (rounds x)) => |>. rewrite /ISet.subset /ISet.iset AuxFSet.subset_id => |>*. rewrite /ISet.mem iset_in_def in H0 => |>. qed.

  (* Global Protocol *)

  op protocol_round (round:round) (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) (ins:in_msgs pmap) : pmsgs pmap =
    let xs = P.zip3 ws rs ins in
    P.imap (fun i (wi_ri_insi:_*(_*_)) => local_protocol_round i round x wi_ri_insi.`1 wi_ri_insi.`2.`1 wi_ri_insi.`2.`2) xs.

  op protocol_end (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) (ins:in_msgs pmap) : local_output pmap =
    let xs = P.zip3 ws rs ins in
    P.imap (fun i (wi_ri_insi:_*(_*_)) => local_protocol_end i x wi_ri_insi.`1 wi_ri_insi.`2.`1 wi_ri_insi.`2.`2) xs.

  op protocol''' (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) (ins:in_msgs pmap) (round1 d:round) : in_msgs pmap =
    foldl (fun ins (round:round) => pprset ins round (ppswap (protocol_round round x ws rs ins))) ins (iota_ round1 d).

  op protocol'' (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) (ins:in_msgs pmap) (rounds:round) : in_msgs pmap =
    foldl (fun ins (round:round) => pprset ins round (ppswap (protocol_round round x ws rs ins))) ins (iseq rounds).

  op protocol' (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) : in_msgs pmap =
    protocol'' x ws rs (pprempty (rounds x) witness) (rounds x).

  op protocol (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) : trace * local_output pmap =
    let ins = protocol' x ws rs in
    let outs = protocol_end x ws rs ins in
    let tr = P.zip ws (P.zip ins rs) in
    (tr,outs).

  (* protocol execution shall ignore future messages *)
  lemma protocol_round_pprmsgs_up_to sz n n2 x ws rs ins :
    pprdom sz n2 ins /\ 0 <= n /\ n <= n2 /\ n < sz /\ n2 <= sz =>
      protocol_round n x ws rs ins = protocol_round n x ws rs (pprmsgs_up_to n ins).
    move => |> H0 H1 H2 H3 H4. rewrite /protocol_round pmap_eqP => |>y Hy. 
    rewrite !get_pinit !Hy => |>. rewrite !get_pzip3 !Hy => |>. 
    rewrite get_pprmsgs_up_to => |>. rewrite (local_protocol_round_prmsgs_up_to sz _ n n) => |>.
    move => i Hi. move :H0. rewrite /pprdom P.allP => |>Hi2. have : prdom sz n2 ((P.get ins y)). rewrite Hi2 => |>. move :Hy. rewrite /ISet.mem iset_in_def => |>. rewrite /prdom P.allP => |>J. have : rdom sz n2 ((P.get ((P.get ins y)) i)). rewrite J => |>. move :Hi. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. smt(). qed.

  lemma protocol_round_prefix n x ws rs (ins1 ins2:in_msgs pmap) :
    (forall r, 0 <= r < n => pprget ins1 r = pprget ins2 r) =>
    0 <= n => 
      protocol_round n x ws rs ins1 = protocol_round n x ws rs ins2.
    move => |> H H0. rewrite /protocol_round pmap_eqP => |>y Hy. 
    rewrite !get_pinit !Hy => |>. rewrite !get_pzip3 !Hy => |>. 
    rewrite (local_protocol_round_prefix _ _ _ _ _ (get ins1 y) (get ins2 y) ) => |>. move => r Hr1 Hr2. have : pprget ins1 r = pprget ins2 r. rewrite H => |>. rewrite /pprget => |>. rewrite pmap_eqP => |>V. 
    have : get (ppinit (fun (i j : int) => get (get (get ins1 i) j) r)) y = get (ppinit (fun (i j : int) => get (get (get ins2 i) j) r)) y. rewrite V => |>. rewrite !get_ppinit !Hy => |>. qed.

  lemma oget_protocol_round i n x ws rs ins :
    ISet.mem i partyset => 
      P.get (protocol_round n x ws rs ins) i = local_protocol_round i n x (P.get ws i) (P.get rs i) (P.get ins i).
    rewrite /protocol_round => |>H. rewrite get_pinit H => |>*. rewrite get_pzip3 H => |>*. qed.

  lemma get_protocol_out''' (n n1 d:int) i j x ws rs ins :
    ISet.mem i partyset => ISet.mem j partyset =>
    ! ( n1 <= n < n1+d) =>
    0 <= n1 => 0 <= d =>
    Array.get (P.get (P.get (protocol''' x ws rs ins n1 d) i) j) n =
    Array.get (P.get (P.get ins i) j) n.
    move =>Hi Hj H H0 H1. rewrite /protocol''' => |>. move : H H1. elim/natind:d => |>. 
    move => d H1 H2 H3. rewrite iota0 => |>. 
    move => d H1 R H2 H3. rewrite iota_add => |>. rewrite iota1 => |>. rewrite -rcons_cat => |>. rewrite foldl_rcons => |>. rewrite -R => |>. smt(). clear R.
    rewrite get_pprset Hi => |>. rewrite get_prset Hj=> |>. rewrite /ppswap get_ppinit Hi => |>. rewrite get_pinit Hj => |>. rewrite get_set_neqE => |>. smt(). qed.

  lemma protocol_succ''' x ws rs ins n0 d :
    0 <= n0 /\ 0 <= d => protocol''' x ws rs ins n0 (d + 1) = pprset (protocol''' x ws rs ins n0 d) (n0+d) (ppswap (protocol_round (n0+d) x ws rs (protocol''' x ws rs ins n0 d))).
    rewrite /protocol''' => |>*. rewrite iota_add => |>*. rewrite !iota1 => |>*. rewrite -rcons_cat foldl_rcons => |>*. qed.

  lemma protocol_succ'' x ws rs ins n :
    0 <= n => protocol'' x ws rs ins (n + 1) = pprset (protocol'' x ws rs ins n) n (ppswap (protocol_round n x ws rs (protocol'' x ws rs ins n))).
    rewrite /protocol'' => |>*. rewrite iseq_succ => |>*. rewrite foldl_rcons => |>*. qed.

  lemma pprdom_protocol'' sz x ws rs ins (round:round) :
    0 <= sz => 0 <= round /\ pprdom sz 0 ins =>
      pprdom sz round (protocol'' x ws rs ins round).
    rewrite /protocol'' => Hsz. elim/natind:round => |>H1 H2 H3 H4. rewrite iseq_nil => |>*. smt().
    rewrite iseq_succ => |>H5. rewrite foldl_rcons => |>*. rewrite pprdom_pprset => |>*. rewrite H3 => |>*. qed.

  lemma prdom_get_protocol'' sz i x n ws rs ins :
    0 <= sz => ISet.mem i partyset /\ ISet.mem n (roundset x) /\ pprdom sz 0 ins =>
      prdom sz n (P.get (protocol'' x ws rs ins n) i).
    rewrite /protocol''. elim/natind:n => |>n H1 H2 H3 H4 H5. rewrite iseq_nil => |>*. rewrite pprdom_prdom_get => |>*. move :H4. rewrite /ISet.mem iset_in_def => |>N1 N2. have : n = 0. smt(). progress. 
    rewrite iseq_succ => |>H6. rewrite foldl_rcons => |>. rewrite get_pprset => |>. rewrite (_ : (foldl (fun (ins0 : in_msgs pmap) (round : round) => pprset ins0 round (ppswap (protocol_round round x ws rs ins0))) ins (iseq n)) = protocol'' x ws rs ins n ). rewrite /protocol'' => |>H6. rewrite H4 => |>. rewrite prdom_prset => |>*. rewrite (_: (foldl (fun (ins0 : in_msgs pmap) (round : round) => pprset ins0 round (ppswap (protocol_round round x ws rs ins0))) ins (iseq n)) = protocol'' x ws rs ins n) in H2. rewrite /protocol'' => |>*. rewrite H2 => |>*. move :H5. rewrite /ISet.mem !iset_in_def => |>*. smt(). qed.

  lemma pprdom_protocol' x ws rs :
      pprdom (rounds x) (rounds x) (protocol' x ws rs).
    rewrite /protocol' => |>*. rewrite pprdom_protocol'' => |>*. rewrite rounds_ge0 => |>. rewrite pprdom_pprempty => |>*. rewrite rounds_ge0 => |>*. rewrite rounds_ge0 => |>. qed.

  lemma size_get_get_protocol'' sz i j x ws rs ins round :
    ISet.mem i partyset => ISet.mem j partyset =>
    0 <= sz => pprdom sz 0 ins => 0 <= round =>
    size (P.get (P.get (protocol'' x ws rs ins round) i) j) = sz.
    move => Hi Hj Hsz Hround H. have : pprdom sz round (protocol'' x ws rs ins round). rewrite pprdom_protocol'' => |>.
    rewrite /pprdom allP => |>H0.
    have : prdom sz round (get (protocol'' x ws rs ins round) i). rewrite H0 => |>. move :Hi. rewrite /ISet.mem iset_in_def => |>. rewrite /prdom allP => |>H1.
    have : rdom sz round (get (get (protocol'' x ws rs ins round) i) j). rewrite H1 => |>. move :Hj. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. qed.

  lemma size_get_get_protocol' i j x ws rs :
    ISet.mem i partyset => ISet.mem j partyset =>
    size (P.get (P.get (protocol' x ws rs) i) j) = rounds x.
    have : pprdom (rounds x) (rounds x) (protocol' x ws rs). rewrite pprdom_protocol' => |>.
    rewrite /pprdom allP => |>H Hi Hj. 
    have : prdom (rounds x) (rounds x) (get (protocol' x ws rs) i). rewrite H => |>. move :Hi. rewrite /ISet.mem iset_in_def => |>. rewrite /prdom allP => |>H0.
    have : rdom (rounds x) (rounds x) (get (get (protocol' x ws rs) i) j). rewrite H0 => |>. move :Hj. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. qed.

  lemma split_protocol'' sz n1 n2 x ws rs :
    0 <= n1 /\ n1 <= n2/\ n2 <= sz =>
      protocol'' x ws rs (pprempty sz witness) n2 = protocol''' x ws rs (protocol'' x ws rs (pprempty sz witness) n1) n1 (n2-n1).
    rewrite /protocol'' /protocol''' => |>*. rewrite -foldl_cat => |>*. congr. 
    rewrite /iseq => |>*. rewrite -iota_add => |>*. smt(). congr. algebra. qed.

  lemma prefix_protocol''' sz x ws rs ins n1 d :
    pprdom sz n1 ins /\ 0 <= n1 /\ 0 <= d =>
      pprmsgs_up_to n1 (protocol''' x ws rs ins n1 d) = ins.
    elim/natind:d => |>H1 H2 H3 H4 H5. rewrite /protocol''' => |>*. rewrite iota0 => |>*. rewrite (pprmsgs_up_to_id sz n1 n1) => |>*. 
    rewrite protocol_succ''' => |>H6. rewrite pprmsgs_up_to_lt_set => |>*. progress. smt().
    rewrite H3 => |>*. qed.

  lemma prefix_protocol'' sz x ws rs n n2 :
    0 <= sz =>
    0 <= n /\ n <= n2 /\ n2 <= sz =>
      pprmsgs_up_to n (protocol'' x ws rs (pprempty sz witness) n2) = protocol'' x ws rs (pprempty sz witness) n.
    progress. rewrite (split_protocol'' sz n n2 x ws rs) => |>*. rewrite (prefix_protocol''' sz) => |>*. rewrite pprdom_protocol'' => |>*. rewrite pprdom_pprempty => |>*. smt(). qed.

  lemma get_protocol_prefix_sz'' sz1 sz2 i j x ws rs n r :
    ISet.mem i partyset => ISet.mem j partyset =>
    0 <= n => n < r => r <= sz1 => r <= sz2 => 
    get (P.get (P.get (protocol'' x ws rs (pprempty sz1 witness) r) i) j) n =
    get (P.get (P.get (protocol'' x ws rs (pprempty sz2 witness) r) i) j) n.
    move => Hi Hj H H0 H1.
    move :H H0 H1. elim/natind:r n i j Hi Hj => |>.
    move => r V1 n i j Hi Hj V2 V3 V4 V5. rewrite /protocol'' !iseq_nil => |>. rewrite !get_pprempty !Hi => |>.
    rewrite !get_prempty !Hj => |>. rewrite !get_init => |>.
    move => r V1 R n i j Hi Hj V2 V3 V4 V5. rewrite !protocol_succ'' => |>. rewrite !get_pprset !Hi => |>. rewrite !get_prset !Hj => |>. rewrite /ppswap !get_ppinit !Hi => |>. rewrite !get_pinit !Hj => |>. 
    rewrite !get_setE => |>. rewrite (size_get_get_protocol'' sz1) => |>. smt(). rewrite pprdom_pprempty => |>. smt(). rewrite (size_get_get_protocol'' sz2) => |>. smt(). rewrite pprdom_pprempty => |>. smt(). have : 0 <= n < sz1. smt(). move => H1. have : 0 <= n < sz2. smt(). move => H2. rewrite H1 H2 => |>. case (n=r) => |>. rewrite (protocol_round_prefix r x ws rs (protocol'' x ws rs (pprempty sz1 witness) r) (protocol'' x ws rs (pprempty sz2 witness) r) ) => |>. move => k Hk1 Hk2. rewrite /pprget ppmap_eqP => |>. move => y1 y2 Hy1 Hy2. rewrite !get_ppinit !Hy1 => |>. rewrite !get_pinit !Hy2 => |>. rewrite R => |>. smt(). smt().
    move => V6. rewrite R => |>. smt(). smt(). smt(). qed.
 
  lemma valid_trace_protocol x ws rs :
    valid_trace x (protocol x ws rs).`1.
    rewrite /protocol /valid_trace => |>. rewrite /get_trace_inputs /get_trace_rands /get_trace_in_msgs /snd3 => |>. rewrite /pprdom P.allP => |>i H1 H2. rewrite P.get_map => |>. rewrite !P.get_zip => |>. have : 0 <= i && i < P.size. smt(). move => hip. rewrite !hip => |>*. rewrite pprdom_prdom_get => |>. rewrite /ISet.mem iset_in_def => |>. rewrite pprdom_protocol' => |>. qed.

  (* Consistency *)

  (* from j to i *)
  op get_view_in_msgs (j: party) (vi:view) : rmsgs =
    P.get vi.`2.`1 j.

  (* from i to j*)
  op get_view_out_msgs (i j:party) (x:public_input) (vi:view) : rmsgs = 
    P.get (local_protocol' i x vi) j.

  op consistent_inputs (x:public_input) (i j:party) (i1 i2 : local_input) : bool.
  op consistent_rands (x:public_input) (i j:party) (r1 r2: local_rand) : bool.

  op valid_inputs (x:public_input) (ws:local_input pmap) : bool =
    forall i j, ISet.mem i partyset /\ ISet.mem j partyset => consistent_inputs x i j (P.get ws i) (P.get ws j).
  op valid_rands (x:public_input) (ws:local_rand pmap) : bool =
    forall i j, ISet.mem i partyset /\ ISet.mem j partyset => consistent_rands x i j (P.get ws i) (P.get ws j).

  op consistent_views (x:public_input) (i j:party) (vi vj:view) : bool =
    eq_rmsgs (get_view_in_msgs j vi) (get_view_out_msgs j i x vj) /\ eq_rmsgs (get_view_in_msgs i vj) (get_view_out_msgs i j x vi) /\ consistent_inputs x i j vi.`1 vj.`1 /\ consistent_rands x i j vi.`2.`2 vj.`2.`2. 

  op consistent_trace (x:public_input) (tr:trace) : bool =
    forall i j, ISet.mem i partyset /\ ISet.mem j partyset => consistent_views x i j (get_view i tr) (get_view j tr).

  lemma local_protocol_round_repeat sz i x ws rs ins n :
    rounds x <= sz =>
    ISet.mem i partyset /\ pprdom sz n ins /\ ISet.mem n (roundset x) => 
      local_protocol_round i n x (P.get ws i) (P.get rs i) (P.get (pprset ins n (ppswap (protocol_round n x ws rs ins))) i) = P.get (protocol_round n x ws rs ins) i.
    move =>|> H1 H2 H3 H4. rewrite /protocol_round => |>*. rewrite get_pprset !H2 => |>*. 
    rewrite (local_protocol_round_set sz) => |>*. rewrite pprdom_prdom_get => |>*.
    move :H4. rewrite /ISet.mem iset_in_def => |>. 
    rewrite get_pinit H2 => |>*. rewrite !get_pzip3 !H2 => |>*. qed.

  lemma local_protocol_repeat'' sz i j x ws rs r :
    rounds x <= sz =>
    ISet.mem i partyset /\ ISet.mem j partyset /\ 0 <= r /\ r <= rounds x =>
    P.get (local_protocol'' i x (P.get ws i) (P.get rs i) (P.get (protocol'' x ws rs (pprempty sz witness) r) i) sz r) j = P.get (P.get (protocol'' x ws rs (pprempty sz witness) r) j) i.
    elim/natind: r => |>n N1 N2 N3 N4 N5 N6. rewrite /local_protocol'' /protocol'' => |>. rewrite !iseq_nil => |>. rewrite get_pprempty N4 => |>. rewrite !get_prempty N3 => |>. rewrite N4 => |>. 
    rewrite local_protocol_succ'' => |>N7. rewrite !protocol_succ'' => |>. rewrite !(local_protocol_round_repeat sz) => |>. rewrite pprdom_protocol'' => |>. smt(). rewrite pprdom_pprempty => |>. smt(). rewrite /ISet.mem iset_in_def. smt(). rewrite !get_pprset !N5 !N4 => |>*.
    rewrite !get_pinit N5 N4 => |>. rewrite local_protocol_set'' => |>. smt(). have : pprdom sz n (protocol'' x ws rs (pprempty sz witness) n). rewrite pprdom_protocol'' => |>. smt(). rewrite pprdom_pprempty => |>. smt(). progress. rewrite (pprdom_prdom_get _ n) => |>*. smt(). rewrite N2 => />. smt(). rewrite /protocol'' !get_pinit !N4 => />. qed.

  lemma local_protocol_snd_repeat i c ws rs :
    ISet.mem i partyset =>
    (local_protocol i c (P.get (protocol c ws rs).`1 i)).`2 = P.get (protocol c ws rs).`2 i.
    move => H. have : 0 <= i && i < P.size. move :H. rewrite /ISet.mem iset_in_def => |>*. move => idom.
    rewrite /local_protocol /protocol /protocol' /protocol_end => |>*. rewrite P.get_imap => |>*. rewrite !P.get_zip3 => |>*. rewrite !idom => |>*. qed.

  lemma global_consistency x ws rs :
    valid_inputs x ws /\ valid_rands x rs => consistent_trace x (protocol x ws rs).`1.
    rewrite /consistent_trace /protocol /get_view => |>H1 H2 i j H3 H4. rewrite !P.get_zip => |>*. have : 0 <= i && i < P.size. move :H3. rewrite /ISet.mem iset_in_def => |>*. have : 0 <= j && j < P.size. move :H4. rewrite /ISet.mem iset_in_def => |>*. move => domj domi. rewrite domj domi => |>*.
    rewrite /consistent_views /get_view_in_msgs /get_view_out_msgs => |>*. rewrite /local_protocol' => |>*. rewrite local_protocol_repeat'' => |>*. rewrite rounds_ge0 => |>*.
    rewrite /get_view_in_msgs /get_view_out_msgs. rewrite local_protocol_repeat'' => |>*. rewrite rounds_ge0 => |>*.
    rewrite /valid_inputs in H1. rewrite /valid_rands in H2. rewrite H1 => |>*. rewrite H2 => |>*. split.
    rewrite /eq_rmsgs. rewrite !all_iseqE !allP => |>y. rewrite in_iseq => |>HY1 HY2. rewrite eq_msgP => |>*.
    rewrite /eq_rmsgs. rewrite !all_iseqE !allP => |>y. rewrite in_iseq => |>HY1 HY2. rewrite eq_msgP => |>*. qed.

  lemma global_consistency' x ws rs tr i j :
    ISet.mem i partyset => ISet.mem j partyset =>
    tr = (protocol x ws rs).`1 =>
    valid_inputs x ws => valid_rands x rs => consistent_views x i j (get_view i tr) (get_view j tr).
    move => ? ? ? ? ?. smt(global_consistency). qed.

  lemma local_inputs_consistency (tr:trace) :
    get_trace_inputs tr = P.map fst3 tr.
    rewrite /get_trace_inputs => |>*. qed.

  lemma local_rands_consistency (tr:trace) :
    get_trace_rands tr = P.map thr3 tr.
    rewrite /get_trace_rands => |>*. qed.

  lemma local_protocol_round_consistency x tr n :
    valid_trace x tr /\ consistent_trace x tr /\ ISet.mem n (roundset x) => 
    ppswap (protocol_round n x (get_trace_inputs tr) (get_trace_rands tr) (get_trace_in_msgs_up_to n tr)) = get_trace_in_msgs_round n tr.
    progress. rewrite ppmap_eqP => |>x0 y H2 H3. rewrite get_get_ppswap. rewrite H2 H3 => |>*. rewrite oget_protocol_round. rewrite H3 => |>*. rewrite /consistent_trace in H0. have : consistent_views x x0 y (get_view x0 tr) (get_view y tr). rewrite H0 => |>*. rewrite /get_view /consistent_views /get_view_in_msgs /get_view_out_msgs eq_rmsgsP => |>H4 H5 H6 H7. rewrite /get_trace_in_msgs_up_to. rewrite get_pprmsgs_up_to. rewrite H3 => |>*. rewrite -(local_protocol_round_prmsgs_up_to (rounds x) _ n n) => |>. move => i Hi. rewrite /get_trace_in_msgs get_map => |>. move :H3. rewrite /mem -memE iset_in_def => />. 
    move :H. rewrite /valid_trace /pprdom P.allP => |>H. have : prdom (rounds x) (rounds x) ((P.get (get_trace_in_msgs tr) y)). rewrite H => |>. move :H3. rewrite /ISet.mem iset_in_def => |>. rewrite /prdom P.allP => |>HH. have : rdom (rounds x) (rounds x) ((P.get ((P.get (get_trace_in_msgs tr) y)) i)). rewrite HH => |>. move :Hi. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom /get_trace_in_msgs get_pmap => |>. move :H1. rewrite /ISet.mem iset_in_def => |>. smt(). 
    rewrite (local_inputs_consistency tr) => |>*. rewrite (local_rands_consistency tr) => |>*. rewrite get_pmap => |>*. rewrite /fst3 /snd3 /thr3 => |>*. rewrite /prget get_pinit H3 => |>*. rewrite /get_trace_in_msgs_round => |>*. rewrite get_pinit H3 => |>*. 
    have : prdom (rounds x) (rounds x) (P.get tr y).`2.`1. rewrite valid_get_get_trace_in_msgs => |>*. move => dom. rewrite local_protocol_prget''. progress. rewrite /get_trace_in_msgs /snd3 => |>*. rewrite get_prget H2 => |>*. rewrite get_pprget /snd3 H2 => |>*. rewrite /get_trace_in_msgs /snd3 get_prget H3 => |>*. rewrite get_pmap => |>*.
    rewrite H4 => />. qed.

  lemma local_protocol_consistency'' x tr r :
    valid_trace x tr /\ consistent_trace x tr /\ 0 <= r /\ r <= rounds x =>
      protocol'' x (get_trace_inputs tr) (get_trace_rands tr) (pprempty (rounds x) witness) r = get_trace_in_msgs_up_to r tr.
    elim/natind: r => |>r H2 H3 H4 H5 H6. rewrite (get_trace_in_msgs_up_to_neg0 _ _ x) => |>*. rewrite /protocol'' iseq_nil => |>*.
    rewrite protocol_succ'' => |>H7. rewrite !H3 => |>*. smt(). clear H3. rewrite (get_trace_in_msgs_up_to_succ _ x) => |>*. rewrite /ISet.mem iset_in_def. smt(). congr. rewrite local_protocol_round_consistency => |>*. rewrite /roundset /ISet.mem iset_in_def. smt(). qed.

  lemma local_protocol_consistency' x (tr:trace) :
    valid_trace x tr /\ consistent_trace x tr /\ 0 <= rounds x /\ rounds x <= rounds x =>
      protocol' x (get_trace_inputs tr) (get_trace_rands tr) = get_trace_in_msgs tr.
    progress. rewrite /protocol' => |>*. rewrite local_protocol_consistency'' => |>*.
    rewrite get_trace_in_msgs_up_to_end => |>*. qed.

  lemma local_consistency x tr :
    valid_trace x tr /\ consistent_trace x tr => (protocol x (get_trace_inputs tr) (get_trace_rands tr)).`1 = tr.
    progress. rewrite /protocol => |>*. rewrite (local_inputs_consistency tr) => |>*. rewrite (local_rands_consistency tr) => |>*. rewrite local_protocol_consistency' => |>*. rewrite rounds_ge0. rewrite /get_trace_in_msgs => |>*. rewrite -P.id_zip3 => |>*. qed.

  lemma consistent_trace_inputs x tr :
    consistent_trace x tr => valid_inputs x (get_trace_inputs tr).
    rewrite /consistent_trace /valid_inputs => |>H i j H1 H2. have : consistent_views x i j (get_view i tr) (get_view j tr). rewrite H => |>*. rewrite /consistent_views => |>H3 H4 H5 H6. rewrite /get_trace_inputs => |>*. rewrite P.get_map /fst3 => |>*. move :H1. rewrite /ISet.mem iset_in_def => |>*. rewrite !P.get_map => |>*. move :H2. rewrite /ISet.mem iset_in_def => |>*. qed.

  lemma consistent_trace_rands x tr :
    consistent_trace x tr => valid_rands x (get_trace_rands tr).
    rewrite /consistent_trace /valid_rands => |>H i j H1 H2. have : consistent_views x i j (get_view i tr) (get_view j tr). rewrite H => |>*. rewrite /consistent_views => |>H3 H4 H5 H6. rewrite /get_trace_rands => |>*. rewrite P.get_map /thr3 => |>*. move :H1. rewrite /ISet.mem iset_in_def  => |>*. rewrite !P.get_map => |>*. move :H2. rewrite /ISet.mem iset_in_def => |>*. qed.

  lemma local_global_consistency x tr :
    (valid_trace x tr /\ consistent_trace x tr) = (exists ws rs, valid_inputs x ws /\ valid_rands x rs /\ (protocol x ws rs).`1 = tr).
    rewrite eq_logical. split.
    progress. exists (get_trace_inputs tr) (get_trace_rands tr). progress.
    rewrite consistent_trace_inputs => |>*. rewrite consistent_trace_rands => |>*. 
    rewrite local_consistency => |>*. 
    progress. rewrite valid_trace_protocol => |>*.  rewrite global_consistency => |>*. qed.

  (* Pairwise view consistency closer to MitH version *)

  op pairwise_consistent_views x i j vi vj =
    valid_view x vi /\ valid_view x vj /\ consistent_views x i j vi vj.

  op pairwise_consistent_trace x tr : bool =
    forall i j, ISet.mem i partyset /\ ISet.mem j partyset => pairwise_consistent_views x i j (get_view i tr) (get_view j tr).

  lemma equiv_pairwise_consistency x tr :
    pairwise_consistent_trace x tr = (valid_trace x tr /\ consistent_trace x tr).
    rewrite /valid_trace /pairwise_consistent_trace /pairwise_consistent_views /consistent_trace => |>*. rewrite eq_logical => |>*. split. move => H. split. 
    rewrite /pprdom P.allP => |>i H1 H2. rewrite /prdom P.allP => |>j H3 H4. have : valid_view x (get_view i tr) /\ valid_view x (get_view j tr) /\ consistent_views x i j (get_view i tr) (get_view j tr). rewrite H => |>. rewrite /ISet.mem !iset_in_def => |>*. 
    rewrite /valid_view /get_trace_in_msgs /get_view => |>*. rewrite P.get_map /snd3 => |>*. rewrite prdom_rdom_get => |>*. rewrite /ISet.mem iset_in_def => |>*. 
    move => i j H1 H2.
    have : valid_view x (get_view i tr) /\ valid_view x (get_view j tr) /\ consistent_views x i j (get_view i tr) (get_view j tr). rewrite H => |>. rewrite !/valid_view /get_view => |>*.  
    move => H1 H2 i j H3 H4. have : consistent_views x i j (get_view i tr) (get_view j tr). rewrite H2 => |>*. rewrite /consistent_views eq_rmsgsP => |>H5 H6 H7 H8. 
    move :H1. rewrite /pprdom /get_trace_in_msgs P.allP /valid_view => |>H1. have : prdom (rounds x) (rounds x) (P.get (P.map snd3 tr) i). rewrite H1 => |>. move :H3. rewrite /ISet.mem iset_in_def => |>. rewrite /get_view P.get_map /snd3 => |>. move :H3. rewrite /ISet.mem iset_in_def => |>H9.
    have : prdom (rounds x) (rounds x) ((P.get ((P.map (fun (x0 :_*(_*_)) => snd3 x0) tr)) j)). rewrite H1 => |>. move :H4. rewrite /ISet.mem iset_in_def => |>. rewrite /get_view P.get_map /snd3 => |>. move :H4. rewrite /ISet.mem iset_in_def => |>. qed.

  lemma pairwise_global_consistency' x ws rs tr i j :
    ISet.mem i partyset => ISet.mem j partyset =>
    tr = (protocol x ws rs).`1 =>
    valid_inputs x ws => valid_rands x rs => pairwise_consistent_views x i j (get_view i tr) (get_view j tr).
    move => H H0 H1 H2 H3. rewrite /pairwise_consistent_views. rewrite (global_consistency' x ws rs tr i j) => |>*. have : valid_trace x (protocol x ws rs).`1. rewrite valid_trace_protocol => |>*. rewrite /valid_trace /get_view !H1 /get_trace_in_msgs !/valid_view /snd3 => |>H4. 
    move :H4. rewrite /pprdom P.allP => |>H5. 
    have : prdom (rounds x) (rounds x) ((P.get ((P.map (fun (x0 : local_input * (in_msgs * local_rand)) => x0.`2.`1) (protocol x ws rs).`1)) i)). rewrite H5 => |>. move :H. rewrite /ISet.mem iset_in_def => |>. rewrite P.get_map => |>. move :H. rewrite /ISet.mem iset_in_def => |>. move => H6.
    have : prdom (rounds x) (rounds x) ((P.get ((P.map (fun (x0 : local_input * (in_msgs * local_rand)) => x0.`2.`1) (protocol x ws rs).`1)) j)). rewrite H5 => |>. move :H0. rewrite /ISet.mem iset_in_def => |>. rewrite P.get_map => |>. move :H0. rewrite /ISet.mem iset_in_def => |>. qed.

  lemma pairwise_local_global_consistency x tr :
    pairwise_consistent_trace x tr = (exists ws rs, valid_inputs x ws /\ valid_rands x rs /\ (protocol x ws rs).`1 = tr).
    rewrite equiv_pairwise_consistency local_global_consistency => |>*. qed.

  (* Protocol consistency *)

  op view_output (i:party) (x:public_input) (v:view) : local_output =
    local_protocol_end i x v.`1 v.`2.`2 v.`2.`1.
  op view_outputs (x:public_input) (vs:view T.pmap) : local_output T.pmap =
    P.imap (fun i v => view_output i x v) vs.

  (* emulating the protocol locally is equivalent to the local projection of a protocol run *)
  lemma protocol_consistency cs x ws :
    view_outputs x (protocol x ws cs).`1 = (protocol x ws cs).`2.
    rewrite /view_outputs /view_output /protocol /protocol' /protocol_end => |>*. 
    rewrite pmap_eqP => |>i H. rewrite !get_pimap => |>*. rewrite !get_pzip3 => |>*. rewrite !H => |>*. qed.

end Protocol.
