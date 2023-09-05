require import Int IntDiv List.
require import Aux AuxList.

theory SecretSharingScheme.
  
  const n : {int | 2 <= n} as n_pos.
  const t : {int | 0 <= t < n } as t_pos.

  type pid_t.
  op pid_set : pid_t list.
  axiom pid_set_size : size pid_set = n.
  axiom pid_set_uniq : uniq pid_set.

  type secret_t.
  type share_t.
  type shares_t = (pid_t * share_t) list.
  type rand_t.
  type public_t.

  op secret_public : secret_t -> public_t.
  op share_public : share_t -> public_t.
  op shares_public : shares_t -> public_t.

  op get_party_share (pid:pid_t) (ss:shares_t) : share_t = oget (assoc ss pid).

  op valid_secret : secret_t -> bool.
  op valid_rand : rand_t -> public_t -> bool.
  op consistent_shares : pid_t -> pid_t -> share_t -> share_t -> bool.
  op valid_shares (ss:shares_t) : bool =
    unzip1 ss = pid_set /\ all (fun i => all (fun j => consistent_shares i j (get_party_share i ss) (get_party_share j ss)) pid_set) pid_set.
  
  op share : rand_t -> secret_t -> shares_t.
  op public_encoding : secret_t -> shares_t.
  op pub_reconstruct : pid_t -> share_t -> secret_t.
  op reconstruct : shares_t -> secret_t.
  op reconstruct_rand : shares_t -> rand_t.

  (* for MitH *)
  op in_rng_share (ws:shares_t) : bool =
    exists r w, valid_rand r (secret_public w) /\ valid_secret w /\ share r w = ws.

  axiom size_pid_set : size pid_set = n.
  axiom correct (r : rand_t) (s : secret_t) :
    valid_rand r (secret_public s) =>
    valid_secret s => reconstruct (share r s) = s.
  axiom unzip1_share (r : rand_t) (s : secret_t) :
    unzip1 (share r s) = pid_set.
  lemma size_share (r : rand_t) (s : secret_t) :
    size (share r s) = n.
    have : size (unzip1 (share r s)) = n. rewrite unzip1_share => />. rewrite size_pid_set => />. rewrite size_map => />. qed.
  axiom public_encoding_correct x :
    valid_secret x =>
    reconstruct (public_encoding x) = x.
  axiom unzip1_public_encoding (s : secret_t) :
    unzip1 (public_encoding s) = pid_set.
  lemma size_public_encoding (s : secret_t) :
    size (public_encoding s) = n.
    have : size (unzip1 (public_encoding s)) = size pid_set. rewrite unzip1_public_encoding => |>. rewrite size_map => />. move => H. rewrite H size_pid_set => />. qed.
  axiom public_encoding_inj x y : valid_secret x => valid_secret y =>
    public_encoding x = public_encoding y => x = y.
  axiom public_encoding_reconstruct (s : secret_t) :
    forall pid, pid \in pid_set => pub_reconstruct pid (oget (assoc (public_encoding s) pid)) = s.
  axiom valid_reconstruct ss :
    valid_shares ss => valid_secret (reconstruct ss) /\ valid_rand (reconstruct_rand ss) (secret_public (reconstruct ss)).
  lemma valid_secret_reconstruct ss :
    valid_shares ss => valid_secret (reconstruct ss). smt(valid_reconstruct). qed.
  lemma valid_rand_reconstruct ss:
    valid_shares ss => valid_rand (reconstruct_rand ss) (secret_public (reconstruct ss)). smt(valid_reconstruct). qed.
  axiom valid_share r s :
    valid_secret s => valid_rand r (secret_public s) => valid_shares (share r s).    
  axiom complete ss :
    valid_shares ss =>
    share (reconstruct_rand ss) (reconstruct ss) = ss.   
  axiom valid_public_encoding x :
    valid_secret x =>
    valid_shares (public_encoding x).
  lemma public_encoding_rand x :
    valid_secret x => (exists r, valid_rand r (secret_public x) /\ share r x = public_encoding x).
    move => H. exists (reconstruct_rand (public_encoding x)) => />.
    have : valid_secret (reconstruct (public_encoding x)) /\ valid_rand (reconstruct_rand (public_encoding x)) (secret_public (reconstruct (public_encoding x))). rewrite valid_reconstruct => |>. rewrite valid_public_encoding => |>. move => |> H1 H2.
    rewrite public_encoding_correct in H2 => |>.
    rewrite (_:share (reconstruct_rand (public_encoding x)) x = share (reconstruct_rand (public_encoding x)) (reconstruct (public_encoding x))). 
    rewrite (public_encoding_correct x) => |>. rewrite complete => |>. rewrite valid_public_encoding => |>. qed.

  (* for MitH *)
  lemma valid_shares_bij ss :
    in_rng_share ss = valid_shares ss.
    rewrite /in_rng_share => |>. rewrite eq_logical => |>. split.
    move => r s H H0. rewrite valid_share => |>.
    move => H. exists (reconstruct_rand ss) (reconstruct ss) => |>. have : valid_secret (reconstruct ss) /\ valid_rand (reconstruct_rand ss) (secret_public (reconstruct ss)). rewrite valid_reconstruct => |>. move => |>H0 H1. rewrite complete => |>. qed.
  
end SecretSharingScheme.

theory ListSecretSharingScheme.

  clone import SecretSharingScheme as SS.
    
  op to_pids_t pids (ss: SS.shares_t list) : (pid_t*(SS.share_t list)) list = 
    map (fun pid => (pid, map (SS.get_party_share pid) ss)) pids.
  op size_pids_t (xs:(pid_t*(SS.share_t list)) list) : int =
    oapp (fun (ix:_*_) => size ix.`2) 0 (onth xs 0).
  op from_pids_t (xs:(pid_t*(SS.share_t list)) list) : SS.shares_t list =
    map (fun i => map (prod idfun (fun x => nth witness x i)) xs) (iseq (size_pids_t xs)).

  op list_consistent_shares i j (xs ys : SS.share_t list) : bool =
    size xs = size ys /\ all (fun (xy:_*_) => SS.consistent_shares i j xy.`1 xy.`2) (zip xs ys).
  op list_valid_shares (ss: (pid_t * (SS.share_t list)) list ) : bool =
    unzip1 ss = pid_set /\ all (fun i => all (fun j => list_consistent_shares i j (oget (assoc ss i)) (oget (assoc ss j))) pid_set) pid_set.

  axiom n_gt0 : 0 < SS.n.

  lemma size_pids_t_ge0 xs :
    0 <= size_pids_t xs. 
    rewrite /size_pids_t => />. case (onth xs 0) => />x. rewrite size_ge0 => />. qed.

  lemma size_from_pids_t (xs:(pid_t*(SS.share_t list)) list) :
    list_valid_shares xs =>
    size (from_pids_t xs) = size_pids_t xs.
    rewrite /from_pids_t => />. rewrite size_map => />. rewrite size_iseq => />. rewrite /size_pids_t => />H H0.
    have : size xs = n. have : size (unzip1 xs) = size pid_set. rewrite H => />. rewrite size_map size_pid_set => />. move => sz.
    rewrite !(onth_nth witness) => />. rewrite sz n_gt0 => />. rewrite ge0_max => />. rewrite size_ge0 => />. qed.

  lemma size_to_pids_t xs pids : 
    0 < size pids => size_pids_t (to_pids_t pids xs) = size xs.
    move => Sz. rewrite /size_pids_t /to_pids_t => />. rewrite onth_map /get_party_share => />.
    rewrite (onth_nth witness) => />. rewrite !size_map => />. qed.

  lemma valid_to_pids_t xs :
    all SS.valid_shares xs => list_valid_shares (to_pids_t pid_set xs).
    rewrite /valid_shares /list_valid_shares /to_pids_t !allP => />H. rewrite -map_comp /(\o) => />. rewrite map_id => />. move => x Hx. rewrite allP => />i Hi. rewrite !assoc_map_r Hx Hi => />. rewrite /get_party_share !size_map => />. rewrite allP => />j.
    rewrite in_nth => />k. rewrite size_zip !size_map min_eq => />Hk1 Hk2. rewrite !nth_onth !(onth_nth (witness,witness)) => />. rewrite size_zip !size_map min_eq => />. rewrite !nth_zip => />. rewrite !size_map => />. rewrite !(nth_map witness) => />. 
    have : unzip1 (nth witness xs k) = pid_set /\ all (fun (i : pid_t) => all (fun (j : pid_t) => consistent_shares i j (get_party_share i (nth witness xs k)) (get_party_share j (nth witness xs k))) pid_set) pid_set. rewrite H => />. rewrite nth_in => />. clear H. rewrite allP => />H H0.
    have : all (fun (j0 : pid_t) => consistent_shares x j0 (get_party_share x (nth witness xs k)) (get_party_share j0 (nth witness xs k))) pid_set. rewrite H0 => />. clear H0. rewrite allP => />H0. 
    have : consistent_shares x i (get_party_share x (nth witness xs k)) (get_party_share i (nth witness xs k)). rewrite H0 => />. clear H0.
    rewrite /get_party_share => />. qed.

  lemma valid_from_pids_t xs :
    list_valid_shares (xs) => all SS.valid_shares (from_pids_t xs).
    rewrite /list_valid_shares /valid_shares /from_pids_t !allP => />H H0 x. rewrite in_nth => />i. rewrite !size_map size_iseq => />. rewrite ge0_max => />. rewrite size_pids_t_ge0 => />. move => Hi1 Hi2.
    rewrite !(nth_map witness) => />. rewrite !size_iseq => />. rewrite ge0_max => />. rewrite size_pids_t_ge0 => />. rewrite -!map_comp /(\o) => />. 
    rewrite !allP => />k1 Hk1. rewrite allP => />k2 Hk2.
    have : size xs = n. have : size (unzip1 xs) = size pid_set. rewrite H => />. rewrite size_map size_pid_set => />. move => sz.
    have : size_pids_t xs = size (oget (assoc xs k1)). rewrite /size_pids_t => />. rewrite !(onth_nth witness) => />. rewrite sz n_gt0 => />. have : all (fun (j : pid_t) => list_consistent_shares (nth witness xs 0).`1 j (oget (assoc xs (nth witness xs 0).`1)) (oget (assoc xs j))) pid_set. rewrite H0 => />. rewrite -H => />. move :sz. clear H H0 Hi2. case xs => />. smt(n_gt0). rewrite allP => />H1. have : list_consistent_shares (nth witness xs 0).`1 k1 (oget (assoc xs (nth witness xs 0).`1)) (oget (assoc xs k1)). rewrite H1 => />. clear H1. rewrite /list_consistent_shares => />H1 H2. rewrite -H1 => />. rewrite (unzip1_eq_nth _ pid_set) => />. rewrite sz n_gt0 => />. rewrite -H => />. rewrite !(nth_map witness) => />. rewrite sz n_gt0 => />. rewrite assoc_nth_some => />. rewrite sz n_gt0 => />. rewrite H pid_set_uniq => />. move => Sz.
    have : all (fun (j : pid_t) => list_consistent_shares k1 j (oget (assoc xs k1)) (oget (assoc xs j))) pid_set. rewrite H0 => />. clear H0. rewrite allP => />H0. 
    have : list_consistent_shares k1 k2 (oget (assoc xs k1)) (oget (assoc xs k2)). rewrite H0 => />. clear H0. rewrite /list_consistent_shares /get_party_share allP => />H0 H1.
    rewrite !assoc_map_prod => />. rewrite !omap_some => />. rewrite assocTP => />. rewrite H => />. rewrite assocTP => />. rewrite H => />. rewrite !(nth_iseq) !Hi1 !Hi2 => />.
    pose p := ((nth witness (oget (assoc xs k1)) i),(nth witness (oget (assoc xs k2)) i)).
    have : consistent_shares k1 k2 p.`1 p.`2. rewrite H1 => />. rewrite in_nth => />. rewrite size_zip => />. rewrite H0 => />. rewrite min_eq /p => />. exists i => />. rewrite !(nth_onth) !(onth_nth (witness,witness)) => />. rewrite !size_zip H0 min_eq => />. rewrite -H0 -Sz => />.
    rewrite -H0 -Sz => />. rewrite nth_zip => />. rewrite !(onth_nth witness) => />. rewrite -Sz => />. rewrite -H0 -Sz => />. 
    rewrite /p => />. qed.

  lemma from_to_pids_t xs :
    all SS.valid_shares xs => from_pids_t (to_pids_t pid_set xs) = xs.
    move => H. apply (eq_from_nth witness) => />. rewrite size_from_pids_t => |>. rewrite valid_to_pids_t => |>. rewrite size_to_pids_t => |>. rewrite size_pid_set => />. rewrite n_gt0 => />. move => i. rewrite size_from_pids_t => |>. rewrite valid_to_pids_t => |>. rewrite size_to_pids_t => |>. rewrite size_pid_set //. rewrite n_gt0 //. move => Hi1 Hi2.  
    rewrite /from_pids_t /to_pids_t => |>. rewrite !(nth_map witness) => |>. rewrite size_iseq => |>. rewrite ge0_max => |>. rewrite size_pids_t_ge0 => |>. rewrite /size_pids_t onth_map omap_some => |>. rewrite (onth_nth witness) => />. rewrite size_pid_set n_gt0 => />. rewrite size_map => />. rewrite -!map_comp /(\o) => />.
    apply (eq_from_nth witness) => |>. rewrite size_map => |>. rewrite size_pid_set => />. move :H. rewrite allP /valid_shares => |>H. have : unzip1 (nth witness xs i) = pid_set /\ all (fun (i0 : pid_t) => all (fun (j : pid_t) => consistent_shares i0 j (get_party_share i0 (nth witness xs i)) (get_party_share j (nth witness xs i))) pid_set) pid_set. rewrite H => |>. rewrite nth_in => |>. move => |> H0 H1. have : size (unzip1 (nth witness xs i)) = size pid_set. rewrite H0 => />. rewrite size_map size_pid_set => />. move => H2. rewrite H2 => />.
    move => j. rewrite size_map => />Hj1 Hj2. rewrite !(nth_map witness) => />. rewrite !nth_iseq => />. rewrite /size_pids_t !onth_map /prod /idfun => />. rewrite !(onth_nth witness) => />. rewrite size_pid_set n_gt0 => />. rewrite size_map andaP => />. rewrite !(nth_map witness) /get_party_share => />.
    rewrite eq2 => />. rewrite (unzip1_eq_nth _ pid_set) => />. move :H. rewrite allP /valid_shares => |>H. have : unzip1 (nth witness xs i) = pid_set /\ all (fun (i0 : pid_t) => all (fun (j0 : pid_t) => consistent_shares i0 j0 (get_party_share i0 (nth witness xs i)) (get_party_share j0 (nth witness xs i))) pid_set) pid_set. rewrite H => />. rewrite nth_in => />. move => /> H0 H1.  have : size (unzip1 (nth witness xs i)) = size pid_set. rewrite H0 => />. rewrite size_map size_pid_set => />. move => H4. rewrite H4 => />. move :Hj2. rewrite size_pid_set => />. 
    move :H. rewrite allP /valid_shares => |>H. have : unzip1 (nth witness xs i) = pid_set /\ all (fun (i0 : pid_t) => all (fun (j0 : pid_t) => consistent_shares i0 j0 (get_party_share i0 (nth witness xs i)) (get_party_share j0 (nth witness xs i))) pid_set) pid_set. rewrite H => />. rewrite nth_in => />. move => |>H0 H1.
    move :H. rewrite allP /valid_shares => |>H. have : unzip1 (nth witness xs i) = pid_set /\ all (fun (i0 : pid_t) => all (fun (j0 : pid_t) => consistent_shares i0 j0 (get_party_share i0 (nth witness xs i)) (get_party_share j0 (nth witness xs i))) pid_set) pid_set. rewrite H => />. rewrite nth_in => />. clear H. rewrite !allP => /> H H0.
    rewrite -H => />. rewrite !(nth_map witness) => />. have : size (unzip1 (nth witness xs i)) = size pid_set. rewrite H => />. rewrite size_map size_pid_set => />. move => H4. rewrite H4 => />. move :Hj2. rewrite size_pid_set => />. rewrite assoc_nth_some => />. have : size (unzip1 (nth witness xs i)) = size pid_set. rewrite H => />. rewrite size_map size_pid_set => />. move => H4. rewrite H4 => />. move :Hj2. rewrite size_pid_set => />. rewrite H pid_set_uniq => />. qed.

  lemma to_from_pids_t xs :
    list_valid_shares xs => to_pids_t pid_set (from_pids_t xs) = xs.
    rewrite /list_valid_shares /to_pids_t /from_pids_t !allP => />H H0. 
    have : size xs = n. have : size (unzip1 xs) = size pid_set. rewrite H => />. rewrite size_map => />. rewrite size_pid_set => />. move => sz.
    apply (eq_from_nth witness) => />. rewrite size_map => />. rewrite size_pid_set sz => />. 
    move => i. rewrite size_map => />. rewrite size_pid_set => />Hi1 Hi2. 
    rewrite !(nth_map witness) => />. rewrite size_pid_set => />. rewrite -!map_comp /(\o) /get_party_share => />. rewrite eq2 => />. rewrite -H !(nth_map witness) => />. rewrite sz => />.
    apply (eq_from_nth witness) => />. rewrite size_map => />. rewrite size_iseq => />. rewrite ge0_max => />. rewrite size_pids_t_ge0 => />. rewrite /size_pids_t => />. rewrite (onth_nth witness) => />. rewrite sz n_gt0 => />.
    have :  all (fun (j : pid_t) => list_consistent_shares (nth witness xs 0).`1 j (oget (assoc xs (nth witness xs 0).`1)) (oget (assoc xs j))) pid_set. rewrite H0 => />. rewrite -H => />. rewrite in_nth => />. exists 0 => />. rewrite !(nth_map witness) => />. rewrite sz n_gt0 => />. rewrite size_map => />. rewrite sz n_gt0 => />. rewrite allP => />H1. have : list_consistent_shares (nth witness xs 0).`1 (nth witness xs i).`1 (oget (assoc xs (nth witness xs 0).`1)) (oget (assoc xs (nth witness xs i).`1)). rewrite H1 => />. rewrite -H. rewrite in_nth => />. exists i => />. rewrite !(nth_map witness) => />. rewrite sz => />. rewrite size_map => />. rewrite sz => />. rewrite /list_consistent_shares => />. rewrite !assoc_nth_some => />. rewrite sz => />. rewrite n_gt0 => />. rewrite H pid_set_uniq => />. rewrite sz => />. rewrite H pid_set_uniq => />. 
    move => j. rewrite size_map => />. rewrite size_iseq => />. rewrite ge0_max => />. rewrite size_pids_t_ge0 => />. move => Hj1 Hj2. rewrite !(nth_map witness) => />. rewrite size_iseq => />. rewrite ge0_max => />. rewrite size_pids_t_ge0 => />. rewrite !assoc_map_prod => />. rewrite !assoc_nth_some => />. rewrite sz => />. rewrite H pid_set_uniq => />. rewrite nth_iseq => />. rewrite Hj1 Hj2 => />. qed.

  clone include SecretSharingScheme with
    op n = SS.n,
    op t = SS.t,
    type public_t = SS.public_t list,
    type pid_t = SS.pid_t,
    op pid_set = SS.pid_set,
    type secret_t = SS.secret_t list,
    op valid_secret ss = all SS.valid_secret ss,
    type share_t = SS.share_t list,
    op consistent_shares = list_consistent_shares,
    type rand_t = SS.rand_t list,
    op secret_public = map SS.secret_public,
    op share_public = map SS.share_public,
    op shares_public ss = map SS.shares_public (from_pids_t ss),
    op valid_rand rs ws =
      size rs = size ws /\ all (fun (rs:_*_) => SS.valid_rand rs.`1 rs.`2) (zip rs ws),
    op share rs ss =
      to_pids_t pid_set (map (fun r_s => let (r,s) = r_s in SS.share r s) (zip rs ss)),
    op public_encoding ss =
      to_pids_t pid_set (map (fun s => SS.public_encoding s) ss),
    op pub_reconstruct (i:pid_t) (ss:share_t) : secret_t =
      map (SS.pub_reconstruct i) ss,
    op reconstruct shs =
      map (fun sh => SS.reconstruct sh) (from_pids_t shs),
    op reconstruct_rand shs = 
      map (fun sh => SS.reconstruct_rand sh) (from_pids_t shs)
    proof *.
    realize n_pos. rewrite /n SS.n_pos => />. qed.
    realize t_pos. rewrite /t SS.t_pos => />. qed.
    realize pid_set_size. smt(SS.pid_set_size). qed.
    realize pid_set_uniq. smt(SS.pid_set_uniq). qed.
    realize correct. move => r s H H0.
    rewrite /reconstruct /share => |>.
    have : size r = size s. move :H. rewrite /valid_rand /secret_public => |>. rewrite size_map => |>. move => Sz.
    rewrite from_to_pids_t => |>. rewrite allP => |>x.
    rewrite in_nth => |>. rewrite size_map => |>. rewrite size_zip => |>.
    move => i. rewrite Sz min_eq => |>H1 H2.
    rewrite (nth_map witness) => |>. rewrite size_zip Sz min_eq => |>. 
    rewrite nth_onth !(onth_nth (witness,witness)) => |>. rewrite size_zip Sz min_eq => |>. rewrite nth_zip => |>. 
    rewrite SS.valid_share => |>.
    move :H0. rewrite /valid_secret allP => |>H3. rewrite H3 => |>. rewrite nth_in => |>. 
    move :H. rewrite /valid_rand /secret_public allP => |>Sz' H3. case (i < size r) => |>H4.
    pose pp := ((nth witness r i),secret_public (nth witness s i)). have : valid_rand pp.`1 pp.`2. rewrite H3 => |>. rewrite /pp in_nth => |>. exists i => |>. rewrite size_zip !(nth_onth) !(onth_nth (witness,witness)) => |>. rewrite size_zip !size_map => />. rewrite Sz min_eq => />. rewrite !size_map Sz min_eq => />. rewrite nth_zip => |>. rewrite !(onth_nth witness) => |>. rewrite !(nth_map witness) => />. rewrite /pp => |>. have : false. smt(). progress.
    rewrite -map_comp /(\o) => |>. apply (eq_from_nth witness) => |>. rewrite size_map => |>. rewrite size_zip => |>. rewrite Sz min_eq => |>. move => i. rewrite size_map size_zip Sz min_eq => |>H1 H2. rewrite (nth_map witness) => |>. rewrite size_zip Sz min_eq => |>. rewrite (nth_onth) (onth_nth (witness,witness)) => |>. rewrite size_zip Sz min_eq => |>. rewrite nth_zip => |>. rewrite SS.correct => |>.
    move :H. rewrite /valid_rand /secret_public allP => |>Sz' H3. case (i < size r) => |>H4.
    pose pp := (nth witness r i,secret_public (nth witness s i)). have : valid_rand pp.`1 pp.`2. 
    rewrite H3 => |>. rewrite in_nth /pp => |>. exists i => |>. rewrite size_zip size_map Sz min_eq => |>. rewrite !(nth_onth) !(onth_nth (witness,witness)) => |>. rewrite size_zip size_map Sz min_eq => 
|>. rewrite nth_zip => |>. rewrite !(onth_nth witness) => |>. rewrite !(nth_map witness) => |>. rewrite /pp => |>. have : false. smt(). progress.
    move :H0. rewrite /valid_secret allP => |>H3. rewrite H3 => |>. rewrite nth_in => |>. qed.
    realize size_pid_set. rewrite /pid_set => />. rewrite SS.size_pid_set => />. qed.
    realize unzip1_share. move => r s. rewrite /share /pid_set /to_pids_t => />.
    rewrite -map_comp /(\o) => />. rewrite map_id => />. qed.
    realize public_encoding_correct. move => x V. rewrite /reconstruct /public_encoding => |>. 
    rewrite from_to_pids_t => |>. rewrite all_map /preim allP => |>x0 Hx0. rewrite SS.valid_public_encoding => |>. move :V. rewrite /valid_secret allP => />V. rewrite V => />.
    rewrite -map_comp /(\o) => |>. rewrite -(map_id x).
    apply (eq_from_nth witness) => />. rewrite !size_map => />. move => i. rewrite !size_map => />Hi1 Hi2.
    rewrite !(nth_map witness) => />. rewrite !size_map => />. 
    move :V. rewrite /valid_secret allP => />V.
    rewrite SS.public_encoding_correct => |>. rewrite /idfun V => />. rewrite nth_in => />. qed.
    realize unzip1_public_encoding. move => s. rewrite /public_encoding /to_pids_t => />. 
    rewrite -map_comp /(\o) => |>. rewrite map_id => />. qed.
    realize public_encoding_inj. move => x y. rewrite /public_encoding /to_pids_t => />.
    move => S1 S2.
    move :S1. rewrite /valid_secret allP => />S1. 
    move :S2. rewrite /valid_secret allP => />S2. 
    rewrite map_eq_same => />H.
    have : size x = size y.
    have : map (SS.get_party_share (nth witness pid_set 0)) (map SS.public_encoding x) = map (SS.get_party_share (nth witness pid_set 0)) (map SS.public_encoding y). rewrite H => />. rewrite nth_in => />. rewrite size_pid_set n_gt0 => />. rewrite -!map_comp /(\o) /get_party_share => />H1. clear H. have : size (map (fun (x0 : SS.secret_t) => oget (assoc (public_encoding x0) (nth witness ListSecretSharingScheme.pid_set 0))) x) = size (map (fun (x0 : SS.secret_t) => oget (assoc (public_encoding x0) (nth witness ListSecretSharingScheme.pid_set 0))) y). rewrite H1 => />. rewrite !size_map => />. move => Sz.
    apply (eq_from_nth witness) => />.
    move => i Hi1 Hi2. apply SS.public_encoding_inj => />. rewrite S1 => />. rewrite nth_in => />. rewrite S2 => />. rewrite nth_in => />. rewrite -Sz => />.
    apply (eq_from_nth witness) => />. rewrite !SS.size_public_encoding => />. move => j. rewrite !SS.size_public_encoding => />Hj1 Hj2. 
    pose pid1 := (nth witness (public_encoding (nth witness x i)) j).`1.
    pose pid2 := (nth witness (public_encoding (nth witness y i)) j).`1.
    have : unzip1 (public_encoding (nth witness x i)) = SS.pid_set. rewrite unzip1_public_encoding => />. move => domx.
    have : unzip1 (public_encoding (nth witness y i)) = SS.pid_set. rewrite unzip1_public_encoding => />. move => domy.
    have : pid1 = pid2. rewrite /pid1 /pid2 => />. rewrite !(unzip1_eq_nth _ SS.pid_set) => />. rewrite SS.size_public_encoding => />. rewrite SS.size_public_encoding => />. move => pid12.
    have : map (SS.get_party_share pid1) (map SS.public_encoding x) = map (SS.get_party_share pid1) (map SS.public_encoding y). rewrite H => />. rewrite /pid1 => />. rewrite (unzip1_eq_nth _ SS.pid_set) => />. rewrite SS.size_public_encoding => />. rewrite nth_in => />. rewrite size_pid_set => />. 
    rewrite /get_party_share -!map_comp /(\o) => />. rewrite lsame_eq lsameP => />L.  
    have : osame (fun (x0 y0 : SS.share_t) => x0 = y0)
        (onth (map (fun (x0 : SS.secret_t) => oget (assoc (public_encoding x0) pid1)) x) i)
        (onth (map (fun (x0 : SS.secret_t) => oget (assoc (public_encoding x0) pid1)) y) i). rewrite L => />. rewrite !onth_map => />. clear L. rewrite !(onth_nth witness) => />. rewrite -Sz => />. rewrite /pid => />. rewrite !assoc_nth_some => />. rewrite size_public_encoding => />. rewrite domx => />. rewrite pid_set_uniq => />. rewrite pid12 => />. rewrite !assoc_nth_some => />. rewrite size_public_encoding => />. rewrite domy => />. rewrite pid_set_uniq => />.
    rewrite eq2 => />. qed.
    realize valid_share. move => r ss. rewrite /valid_secret /valid_rand /secret_public /valid_shares /share !allP /to_pids_t size_map => />H H0. rewrite -!map_comp /(\o) => />. rewrite map_id => />. move => H1 i Hi.
    rewrite allP => />j Hj. rewrite /get_party_share => />. rewrite !assoc_map_r => />. rewrite Hi Hj => />. rewrite -!map_comp /(\o) => />. rewrite !size_map => />. rewrite allP => />x.
    rewrite !in_nth => />. move => n. rewrite !size_zip => />. rewrite !size_map => />. rewrite !size_zip => />. rewrite !H0 !min_eq => />. move => />Hn1 Hn2. rewrite !nth_onth !(onth_nth (witness,witness)) => />. rewrite !size_zip => />. rewrite !size_map => />. rewrite !size_zip => />. rewrite !H0 !min_eq => />. rewrite !nth_zip => />. rewrite !size_map => />. rewrite !(nth_map witness) => />. rewrite !size_zip => />. rewrite H0 min_eq => />. rewrite !size_zip => />. rewrite H0 min_eq => />. rewrite !nth_onth !(onth_nth (witness,witness)) => |>. rewrite size_zip H0 min_eq => />. rewrite !nth_zip => />. 
    have : SS.valid_shares (share (nth witness r n) (nth witness ss n)). rewrite SS.valid_share => />. rewrite H => />. rewrite nth_in => />. case (n < size r) => />H2. have : valid_rand (nth witness r n,secret_public (nth witness ss n)).`1  (nth witness r n,secret_public (nth witness ss n)).`2. rewrite H1 => />. rewrite in_nth => />. exists n => />. rewrite size_zip size_map H0 min_eq => />. rewrite !nth_onth !(onth_nth (witness,witness)) => />. rewrite size_zip size_map => />. rewrite H0 min_eq => />. rewrite nth_zip => />. rewrite size_map => />. rewrite !(onth_nth witness) => />. rewrite !(nth_map witness) => />. progress. have : false. smt(). progress.
    rewrite /valid_shares allP /get_party_share => />H2 H3. have : all (fun (j0 : SS.pid_t) => consistent_shares i j0 (oget (assoc (share (nth witness r n) (nth witness ss n)) i)) (oget (assoc (share (nth witness r n) (nth witness ss n)) j0))) SS.pid_set. rewrite H3 => />. clear H3. rewrite allP => />H3. rewrite H3 => />. qed.
    realize public_encoding_reconstruct. move => s pid H.
    rewrite /pub_reconstruct /public_encoding /to_pids_t => />. rewrite assoc_map_r => />. rewrite H => />. rewrite -!map_comp /(\o) /get_party_share => />. rewrite id_map => />x. rewrite SS.public_encoding_reconstruct => />. qed.
    realize valid_reconstruct. move => ss. rewrite /valid_shares /valid_secret /reconstruct_rand /reconstruct /valid_rand => |>. rewrite !allP => />H H0. rewrite !size_map => />. split.
    move => x. rewrite /from_pids_t => />. rewrite -!map_comp /(\o) => />. rewrite in_nth => />i. rewrite !size_map => />. rewrite size_iseq => />. rewrite ge0_max => />. rewrite size_pids_t_ge0 => />. move => Hi1 Hi2. 
    rewrite !(nth_map witness) => />. rewrite size_iseq => />. rewrite ge0_max => />. rewrite size_pids_t_ge0 => />. rewrite nth_iseq => />. rewrite Hi1 Hi2 => />. rewrite SS.valid_secret_reconstruct => |>. rewrite /valid_shares => />. rewrite -map_comp /(\o) !allP => />k1 Hk1. rewrite allP => />k2 Hk2. 
    have : size ss = n. have : size (unzip1 ss) = size ListSecretSharingScheme.pid_set. rewrite H => />. rewrite size_map size_pid_set => />. move => Sz.
    have : size_pids_t ss = size (oget (assoc ss k1)). rewrite /size_pids_t => />. rewrite !(onth_nth witness) => />. rewrite Sz n_gt0 => />. have : all (fun (j : pid_t) => consistent_shares (nth witness ss 0).`1 j (get_party_share (nth witness ss 0).`1 ss) (get_party_share j ss)) ListSecretSharingScheme.pid_set. rewrite H0 => />. rewrite (_:ss=zip (unzip1 ss) (unzip2 ss)). rewrite zip_unzip => />. rewrite (nth_onth) (onth_nth (witness,witness)) => />. rewrite size_zip !size_map => />. rewrite min_eq => />. rewrite Sz n_gt0 => />. rewrite nth_zip => />. rewrite !size_map => />. rewrite H => />. rewrite nth_in => />. rewrite size_pid_set => />. rewrite n_gt0 => />.  rewrite allP => />H4. have : consistent_shares (nth witness ss 0).`1 k1 (get_party_share (nth witness ss 0).`1 ss) (get_party_share k1 ss). rewrite H4 => />. rewrite /consistent_shares /get_party_share => />. rewrite allP /consistent_shares => />H5 H6. move :H5. rewrite assoc_nth_some => />. rewrite Sz n_gt0 => />. rewrite H pid_set_uniq => />. move => Sz12.
    have : all (fun (j : pid_t) => consistent_shares k1 j (get_party_share k1 ss) (get_party_share j ss)) ListSecretSharingScheme.pid_set. rewrite H0 => />. clear H0. rewrite allP => />H0. have : consistent_shares k1 k2 (get_party_share k1 ss) (get_party_share k2 ss). rewrite H0 => />. clear H0. rewrite /get_party_share => />. rewrite allP => />H0 H1. rewrite !assoc_map_prod => />. rewrite !omap_some => />. rewrite assocTP => />. rewrite H => />. rewrite assocTP => />. rewrite H => />.
    pose pp := (nth witness (oget (assoc ss k1)) i,nth witness (oget (assoc ss k2)) i). have : consistent_shares k1 k2 pp.`1 pp.`2. rewrite H1 => />. rewrite /pp => />. rewrite in_nth => />. exists i => />. rewrite !size_zip => />. rewrite H0 min_eq => />. rewrite !nth_onth !(onth_nth (witness,witness)) => />. rewrite size_zip H0 min_eq => />. rewrite -H0 -Sz12 => />. rewrite -H0 -Sz12 => />. rewrite nth_zip => />. rewrite !(onth_nth witness) => />. rewrite -Sz12 => />. rewrite -H0 -Sz12 => />. rewrite /pp => />. 
    move => x. rewrite in_nth => />i. rewrite size_zip !size_map => />. rewrite !size_iseq => />. rewrite !ge0_max => />. rewrite size_pids_t_ge0 => />. rewrite min_eq => />Hi1 Hi2. rewrite !nth_onth !(onth_nth (witness,witness)) => />. rewrite size_zip !size_map => />. rewrite !size_iseq => />. rewrite !ge0_max => />. rewrite size_pids_t_ge0 => />.
    have : list_valid_shares ss. rewrite /list_valid_shares => />. rewrite allP => />k1 Hk1. rewrite allP => />k2 Hk2. have : all (fun (j : pid_t) => consistent_shares k1 j (get_party_share k1 ss) (get_party_share j ss)) ListSecretSharingScheme.pid_set. rewrite H0 => />. clear H0. rewrite !allP => />H0. have : consistent_shares k1 k2 (get_party_share k1 ss) (get_party_share k2 ss). rewrite H0 => />. clear H0. rewrite /consistent_shares /get_party_share => />. rewrite allP => />. move => L.
    rewrite !nth_zip => |>. rewrite !size_map => |>. rewrite !(nth_map witness) => |>. rewrite size_from_pids_t => |>. rewrite size_iseq => />. rewrite ge0_max => />. rewrite size_pids_t_ge0 => />. rewrite size_map size_from_pids_t => />. rewrite size_from_pids_t => />. rewrite size_iseq => />. rewrite ge0_max => />. rewrite size_pids_t_ge0 => />. rewrite !nth_iseq Hi1 Hi2 => />. 
    rewrite SS.valid_rand_reconstruct => />. rewrite -!map_comp /(\o) => />. rewrite !allP => />k1 Hk1. rewrite allP => />k2 Hk2. 
     have : size ss = n. have : size (unzip1 ss) = size ListSecretSharingScheme.pid_set. rewrite H => />. rewrite size_map size_pid_set => />. move => Sz.
    have : size_pids_t ss = size (oget (assoc ss k1)). rewrite /size_pids_t => />. rewrite !(onth_nth witness) => />. rewrite Sz n_gt0 => />. have : all (fun (j : pid_t) => consistent_shares (nth witness ss 0).`1 j (get_party_share (nth witness ss 0).`1 ss) (get_party_share j ss)) ListSecretSharingScheme.pid_set. rewrite H0 => />. rewrite (_:ss=zip (unzip1 ss) (unzip2 ss)). rewrite zip_unzip => />. rewrite (nth_onth) (onth_nth (witness,witness)) => />. rewrite size_zip !size_map => />. rewrite min_eq => />. rewrite Sz n_gt0 => />. rewrite nth_zip => />. rewrite !size_map => />. rewrite H => />. rewrite nth_in => />. rewrite size_pid_set => />. rewrite n_gt0 => />.  rewrite allP => />H4. have : consistent_shares (nth witness ss 0).`1 k1 (get_party_share (nth witness ss 0).`1 ss) (get_party_share k1 ss). rewrite H4 => />. rewrite /consistent_shares /get_party_share => />. rewrite allP /consistent_shares => />H5 H6. move :H5. rewrite assoc_nth_some => />. rewrite Sz n_gt0 => />. rewrite H pid_set_uniq => />. move => Sz12.
    have : all (fun (j : pid_t) => consistent_shares k1 j (get_party_share k1 ss) (get_party_share j ss)) ListSecretSharingScheme.pid_set. rewrite H0 => />. clear H0. rewrite allP => />H0. have : consistent_shares k1 k2 (get_party_share k1 ss) (get_party_share k2 ss). rewrite H0 => />. clear H0. rewrite /get_party_share => />. rewrite allP => />H0 H1. rewrite !assoc_map_prod => />. rewrite !omap_some => />. rewrite assocTP H => />. rewrite assocTP H => />.
    pose pp := (nth witness (oget (assoc ss k1)) i,nth witness (oget (assoc ss k2)) i). have : consistent_shares k1 k2 pp.`1 pp.`2. rewrite H1 => />. rewrite /pp in_nth => />. exists i => />. rewrite !size_zip => />. rewrite H0 min_eq => />. rewrite -H0 -Sz12 => />. rewrite !nth_onth !(onth_nth (witness,witness)) => />. rewrite size_zip -H0 min_eq => />. rewrite -Sz12 => />. rewrite nth_zip => />. rewrite !(onth_nth witness) => />. rewrite -Sz12 => />. rewrite -H0 -Sz12 => />. rewrite /pp => />. qed.
    realize complete. move => ss. rewrite /share /reconstruct_rand /reconstruct => |>H.
    have : size ss = n. have : size (unzip1 ss) = size (ListSecretSharingScheme.pid_set). move :H. rewrite /valid_shares => />H H0. rewrite H => />. rewrite size_map size_pid_set => />. move => H1.
    rewrite -(to_from_pids_t ss). move :H. rewrite /valid_shares /list_valid_shares !allP => />H H0. move => x Hx. rewrite allP => />y Hy. 
    have : all (fun (j : pid_t) => consistent_shares x j (get_party_share x ss) (get_party_share j ss)) ListSecretSharingScheme.pid_set. rewrite H0 => />. clear H0. rewrite !allP => />H0. have : consistent_shares x y (get_party_share x ss) (get_party_share y ss). rewrite H0 => />. clear H0. rewrite /consistent_shares /get_party_share => />. rewrite allP => />H2 H3.
    congr. progress. apply (eq_from_nth witness) => |>. rewrite !size_map => |>. rewrite !size_zip => |>. rewrite !size_map => |>. rewrite to_from_pids_t => |>. move => n. rewrite !size_map => |>. rewrite !size_zip => |>. rewrite !size_map => |>. rewrite from_to_pids_t => |>. rewrite valid_from_pids_t => |>. rewrite to_from_pids_t => |>. rewrite size_iseq => |>. rewrite ge0_max => |>. rewrite size_pids_t_ge0 => |>. move => Hn1 Hn2. 
    rewrite !(nth_map witness) => |>. rewrite !size_zip => |>. rewrite !size_map => |>. rewrite size_iseq => |>. rewrite ge0_max => |>. rewrite size_pids_t_ge0 => |>. rewrite size_iseq => |>. rewrite ge0_max => |>. rewrite size_pids_t_ge0 => |>. 
    rewrite !nth_onth !(onth_nth (witness,witness)) => />. rewrite !size_zip !size_map => />. rewrite !size_iseq !ge0_max => />. rewrite size_pids_t_ge0 => />. rewrite !nth_zip => |>. rewrite !size_map => />. rewrite !(onth_nth witness) => |>. rewrite size_iseq => |>. rewrite ge0_max => |>. rewrite size_pids_t_ge0 => |>. 
    rewrite !(nth_map witness) => |>. rewrite size_from_pids_t => |>. rewrite size_iseq => |>. rewrite ge0_max => |>. rewrite size_pids_t_ge0 => |>.  rewrite size_from_pids_t => |>. rewrite size_iseq => |>. rewrite ge0_max => |>. rewrite size_pids_t_ge0 => |>. 
    rewrite SS.complete => |>. rewrite nth_iseq => |>. rewrite Hn1 Hn2 => |>.
    move :H. rewrite /valid_shares !allP => |>H2 H3. rewrite -map_comp /(\o) => />.
    move => x Hx.
    have : size_pids_t ss = size (oget (assoc ss x)). rewrite /size_pids_t => />. rewrite !(onth_nth witness) => />. rewrite H1 n_gt0 => />. have : all (fun (j : pid_t) => consistent_shares (nth witness ss 0).`1 j (get_party_share (nth witness ss 0).`1 ss) (get_party_share j ss)) ListSecretSharingScheme.pid_set. rewrite H3 => />. rewrite (_:ss=zip (unzip1 ss) (unzip2 ss)). rewrite zip_unzip => />. rewrite (nth_onth) (onth_nth (witness,witness)) => />. rewrite size_zip !size_map => />. rewrite min_eq => />. rewrite H1 n_gt0 => />. rewrite nth_zip => />. rewrite !size_map => />. rewrite H2 => />. rewrite nth_in => />. rewrite size_pid_set => />. rewrite n_gt0 => />.
    rewrite allP => />H4. have : consistent_shares (nth witness ss 0).`1 x (get_party_share (nth witness ss 0).`1 ss) (get_party_share x ss). rewrite H4 => />. rewrite /consistent_shares /get_party_share => />. rewrite allP /consistent_shares => />H5 H6. 
    move :H5. rewrite assoc_nth_some => />. rewrite H1 n_gt0 => />. rewrite H2 pid_set_uniq => />. move => Sz.
    have : all (fun (j : pid_t) => consistent_shares x j (get_party_share x ss) (get_party_share j ss)) ListSecretSharingScheme.pid_set. rewrite H3 => |>. clear H3. rewrite !allP => />H3 y Hy. have : consistent_shares x y (get_party_share x ss) (get_party_share y ss). rewrite H3 => />. clear H3. rewrite /consistent_shares /get_party_share => />. rewrite !assoc_map_prod => |>. rewrite allP => |> H3 H4.
    rewrite !omap_some => />. rewrite assocTP => />. rewrite H2 => />. rewrite assocTP => />. rewrite H2 => />.
    pose p := ((nth witness (oget (assoc ss x)) n),(nth witness (oget (assoc ss y)) n)).
    have : consistent_shares x y p.`1 p.`2. rewrite H4 => />. rewrite /p in_nth => />. exists n => />. rewrite size_zip H3 min_eq => />. rewrite !(nth_onth) !(onth_nth (witness,witness)) => />. rewrite size_zip => />. rewrite H3 min_eq => />. rewrite -H3 -Sz => />. rewrite -H3 -Sz => />. rewrite nth_zip => />. rewrite !(onth_nth witness) => />. rewrite -Sz => />. rewrite -H3 -Sz => />.
    rewrite /p /consistent_shares => />. qed.
    realize valid_public_encoding. rewrite /valid_secret /valid_shares /public_encoding => />x.
    rewrite /to_pids_t -!map_comp /(\o) => />. rewrite map_id !allP => />V i Hi. 
    rewrite allP /get_party_share => />j Hj. rewrite !assoc_map_r !Hi !Hj => />. rewrite !size_map => />. rewrite allP => />k. rewrite in_nth => />. move => n. rewrite !size_zip !size_map min_eq => />Hn1 Hn2. rewrite !(nth_onth) !(onth_nth (witness,witness)) => />. rewrite size_zip !size_map => />. rewrite !nth_zip => />. rewrite !size_map => />.
    rewrite !(nth_map witness) => />. rewrite !size_map => />. rewrite !size_map => />.
    have : valid_shares (public_encoding (nth witness x n)). rewrite SS.valid_public_encoding. rewrite V => />. rewrite nth_in => />. rewrite /valid_shares allP => />H1 H2. 
    have : all (fun (j0 : SS.pid_t) => consistent_shares i j0 (get_party_share i (public_encoding (nth witness x n))) (get_party_share j0 (public_encoding (nth witness x n)))) SS.pid_set. rewrite H2 => />. clear H2. rewrite allP => />H2.
    have : consistent_shares i j (get_party_share i (public_encoding (nth witness x n))) (get_party_share j (public_encoding (nth witness x n))). rewrite H2 => />. clear H2. rewrite /get_party_share => />. qed.

end ListSecretSharingScheme.

