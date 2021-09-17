require import AllCore SmtMap ZModP List FSet Distr.
require import Array5 Array6 Array9 Array10.

require import Aux AuxList AuxFSet AuxSmtMap AuxArray.

require import ASecretSharingScheme.
require import SecretSharingSchemeSecurity.
require import Maurer5Spec.

import Maurer5Spec.
import Maurer5SS.
import PF.

  clone import SecretSharingScheme as MaurerSSS with
    op n = 5,
    op t = 2,
    type pid_t = pid,
    op pid_set = iseq 5,
    type secret_t = val,
    type public_t = unit,
    op valid_secret s = true,
    op consistent_shares= consistent_raw_shares,
    type share_t = shr,
    type rand_t = rand,
    op valid_rand r p = true,
    op secret_public s = tt,
    op share_public s = tt,
    op shares_public ss = tt,
    op public_encoding = (fun (v  : val) => 
            zipl witness MaurerSSS.pid_set (to_list (pshare v))),
    op share = fun (r : rand_t) (v : secret_t) => 
                 zipl witness MaurerSSS.pid_set (to_list (share v r)),
    op reconstruct = fun ss => 
                 unshare (Array5.of_list witness (unzip2 ss)),
    op reconstruct_rand (ss:shares_t) : rand_t = 
      let ss' = Array5.of_list witness (unzip2 ss) in
      rand_shares ss',
    op pub_reconstruct = fun p (ss : shr) => ss.[0]
  proof *.
  realize n_pos by auto.
  realize t_pos by auto.
  realize pid_set_size. rewrite size_iseq => />. qed.
  realize pid_set_uniq. rewrite /pid_set iseq_5 => />. qed.

realize correct.
move => r s; rewrite /valid_rand /valid_secret /reconstruct /share /rshare /unshare /sum_rand /pid_set => /> *. rewrite !array5_to_list_init !iseq_5 => |>. rewrite -!nth0_head !nth_mkseq => |>. 
rewrite !nth_behead => |>. rewrite !nth_mkseq /init_sh => |>. rewrite !(nth_map witness witness) => |>. rewrite size_shr_idx => |>. rewrite size_shr_idx => |>. rewrite size_shr_idx => |>. rewrite size_shr_idx => |>. rewrite size_shr_idx => |>. rewrite size_shr_idx => |>. rewrite size_shr_idx => |>. rewrite size_shr_idx => |>. rewrite size_shr_idx => |>. rewrite size_shr_idx => |>.
rewrite !Array10.initE => |>. rewrite !rng_shr_idx => |>. 
rewrite /shr_idx /Array9.to_list /mkseq  //=.
rewrite (_: iota_ 0 9 = 0::1::2::3::4::5::6::7::8::[]); first by smt(iotaS iota0).
by auto => />; ring.
qed.

realize unzip1_share. move => r s. rewrite /share /rshare /pid_set iseq_5 => |>. qed.

realize public_encoding_correct.
move => x; rewrite /valid_secret /reconstruct /unshare /public_encoding /pshare  /init_sh /shr_idx //=. rewrite !array5_to_list_init /pid_set => |>. 
rewrite !(nth_map witness witness) //=. rewrite size_zipl => />. rewrite size_iseq => />. rewrite size_zipl => />. rewrite size_iseq => />. rewrite size_zipl => />. rewrite size_iseq => />. rewrite !(nth_onth) !onth_zipl => |>. rewrite !nth_mkseq => |>. rewrite /pid_set !iseq_5 => />. ring.
qed.

realize unzip1_public_encoding.
move => x. rewrite /share /rshare /public_encoding /pid_set !iseq_5 => |>. qed.

realize public_encoding_inj.
move => x y. rewrite /valid_secret /public_encoding /pshare => />. rewrite !array5_to_list_init /init_sh => />. rewrite !zipl_zip => />. rewrite !size_mkseq !size_iseq => />. rewrite !size_mkseq !size_iseq => />. rewrite !zip_eq => />. rewrite !size_mkseq !size_iseq => />. rewrite !size_mkseq !size_iseq => />.
rewrite /shr_idx /mkseq => />. 
rewrite (_: iota_ 0 5 = 0::1::2::3::4::[]) //=; first by smt(iotaS iota0).
move => [#] _ _.
rewrite Array6.tP.
move => H.
move : (H 4 _)=> //=.
rewrite /Array9.to_list /mkseq  //=.
rewrite Array6.tP => H1 H2.
by move : (H1 0 _) => //=.
qed. 

realize public_encoding_reconstruct.
move => s pid.
rewrite /pid_set /pub_reconstruct /public_encoding /pshare /pid_set !iseq_5 /init_sh /shr_idx //=.
move => pids. rewrite -!nth0_head !nth_behead => |>. rewrite !assoc_cons !assoc_nil => |>.
elim pids => />pids. elim pids => />pids. elim pids => />pids. elim pids => />pids.
qed.

realize valid_share. rewrite /valid_share /share => |>r s H H0.
rewrite array5_to_list_init => |>. rewrite /valid_shares => |>. rewrite unzip1_zipl => />. rewrite allP => |>i Hi. rewrite allP => |>j Hj. rewrite /get_party_share => |>. rewrite zipl_zip => |>. rewrite size_mkseq => |>. rewrite size_iseq => />. rewrite !assoc_zip => |>. rewrite size_mkseq => |>. rewrite size_iseq => />. rewrite size_mkseq => |>. rewrite size_iseq => />. 
have : forall i, i \in pid_set => index i pid_set = i. move => |> k Hk. rewrite index_iseq => />. move => idx. rewrite !idx => |>. 
have : 0 <= i < 5. move :Hi. rewrite in_iseq => />. move => irng.
have : 0 <= j < 5. move :Hj. rewrite in_iseq => />. move => jrng.
rewrite !(onth_nth witness) => |>. rewrite size_mkseq => |>. move :irng. progress. rewrite size_mkseq => |>. move :jrng. progress. rewrite !nth_mkseq => |>.
rewrite /consistent_shares => |>. rewrite !consistent_raw_shares_share' => |>. qed.
realize complete. move => ss H.
move :H. rewrite /valid_shares => |> H1 H2.
rewrite /share /reconstruct_rand /reconstruct => |>. rewrite array5_to_list_init => |>.
apply (eq_from_nth witness) => |>. rewrite size_zipl => |>. have : size (unzip1 ss) = size pid_set. rewrite H1 => |>. rewrite size_map => |>H3. rewrite H3 => |>.
move => i. rewrite size_zipl /pid_set size_iseq ge0_max => |>Hi1 Hi2. rewrite nth_onth onth_zipl => />. rewrite nth_mkseq => />. rewrite (onth_nth witness) => />. rewrite size_iseq => />. rewrite nth_iseq andaP => />. 
move :H2. rewrite allP => |>H2.
have : size ss = 5. have : size (unzip1 ss) = size pid_set. rewrite H1 => />. rewrite size_map /pid_set size_iseq => />. move => sz.
have : forall i j, 0 <= i < 5 => 0 <= j < 5 =>
consistent_raw_shares i j (nth witness ss i).`2 (nth witness ss j).`2.
move => j k Hj Hk. have : all (fun (k : pid_t) => consistent_shares j k (get_party_share j ss) (get_party_share k ss)) pid_set. rewrite H2 => />. rewrite /pid_set in_iseq => />. smt(). rewrite allP => />H3. have : consistent_shares j k (get_party_share j ss) (get_party_share k ss). rewrite H3 => />. rewrite /pid_set in_iseq => />. smt(). rewrite /consistent_shares /get_party_share => />.
rewrite (_:assoc ss j = assoc (zip (unzip1 ss) (unzip2 ss)) j). rewrite zip_unzip => />. 
rewrite (_:assoc ss k = assoc (zip (unzip1 ss) (unzip2 ss)) k). rewrite zip_unzip => />. 
rewrite !assoc_zip => />. rewrite !size_map => />. rewrite size_map => />. rewrite size_map => />. rewrite !(onth_nth witness) => />. rewrite !H1 size_map /pid_set !index_iseq => />. rewrite in_iseq => />. smt(). move :Hj. rewrite sz => />. rewrite !H1 !index_iseq => />. rewrite in_iseq => />. smt(). rewrite size_map sz => />. smt(). rewrite !(nth_map witness) => />. rewrite !H1 !sz !index_iseq => />. rewrite in_iseq => />. smt(). smt(). rewrite H1 !sz !index_iseq => />. rewrite in_iseq => />. smt(). smt(). rewrite !H1 !index_iseq => />. rewrite !in_iseq => />. smt(). rewrite in_iseq => />. smt(). 
move => H3. clear H2.
rewrite eq2 /init_sh => />. rewrite (unzip1_eq_nth _ pid_set) => />. rewrite sz => />. rewrite nth_iseq Hi1 Hi2 => />.
rewrite Array6.tP => />r Hr1 Hr2. rewrite Array6.get_of_list => />. rewrite (nth_map witness) => />. rewrite size_shr_idx => />. rewrite /rshare => />. rewrite !Array10.initE => />. rewrite !rng_shr_idx => />. rewrite !Array9.initE => />. rewrite /rand_shares => />. rewrite !(nth_map witness) => />. rewrite sz => />. rewrite sz => />. rewrite sz => />. rewrite /shr_idx /sum_rand /unshare => />. rewrite !Array9.of_listK => />. rewrite !(nth_map witness) => />. rewrite sz => />. rewrite sz => />. rewrite sz => />. 
case (i=0) => />.
case (r=0) => />.
case (r=1) => />. algebra. 
case (r=2) => />. 
case (r=3) => />. 
case (r=4) => />. 
case (r=5) => />. 
progress. have : false. smt(). progress.
case (i=1) => />. 
case (r=0) => />.
case (r=1) => />. 
case (r=2) => />. rewrite -(consistent_s01_s12 (nth witness ss 0).`2 (nth witness ss 1).`2) => />. rewrite H3 => />. algebra.
case (r=3) => />. 
case (r=4) => />. rewrite (consistent_s02_s14 (nth witness ss 0).`2 (nth witness ss 1).`2) => />. rewrite H3 => />.
case (r=5) => />. rewrite (consistent_s03_s15 (nth witness ss 0).`2 (nth witness ss 1).`2) => />. rewrite H3 => />.
progress. have : false. smt(). progress.
case (i=2) => />.
case (r=0) => />. rewrite (consistent_s05_s20 (nth witness ss 0).`2 (nth witness ss 2).`2) => />. rewrite H3 => />.
case (r=1) => />.  
case (r=2) => />. rewrite (consistent_s11_s22 (nth witness ss 1).`2 (nth witness ss 2).`2) => />. rewrite H3 => />.
case (r=3) => />. rewrite (consistent_s00_s23 (nth witness ss 0).`2 (nth witness ss 2).`2) => />. rewrite H3 => />.
case (r=4) => />. rewrite -(consistent_s01_s24 (nth witness ss 0).`2 (nth witness ss 2).`2) => />. rewrite H3 => />. algebra.
case (r=5) => />. rewrite (consistent_s13_s25 (nth witness ss 1).`2 (nth witness ss 2).`2) => />. rewrite H3 => />.
progress. have : false. smt(). progress.
case (i=3) => />.
case (r=0) => />. rewrite (consistent_s13_s30 (nth witness ss 1).`2 (nth witness ss 3).`2) => />. rewrite H3 => />.
case (r=1) => />. rewrite (consistent_s02_s31 (nth witness ss 0).`2 (nth witness ss 3).`2) => />. rewrite H3 => />.
case (r=2) => />. rewrite (consistent_s04_s32 (nth witness ss 0).`2 (nth witness ss 3).`2) => />. rewrite H3 => />.
case (r=3) => />. rewrite (consistent_s05_s33 (nth witness ss 0).`2 (nth witness ss 3).`2) => />. rewrite H3 => />.
case (r=4) => />. rewrite (consistent_s21_s34 (nth witness ss 2).`2 (nth witness ss 3).`2) => />. rewrite H3 => />.
case (r=5) => />. rewrite (consistent_s10_s35 (nth witness ss 1).`2 (nth witness ss 3).`2) => />. rewrite H3 => />.
progress. have : false. smt(). progress.
case (i=4) => />.
case (r=0) => />. rewrite (consistent_s03_s40 (nth witness ss 0).`2 (nth witness ss 4).`2) => />. rewrite H3 => />.
case (r=1) => />. rewrite (consistent_s04_s41 (nth witness ss 0).`2 (nth witness ss 4).`2) => />. rewrite H3 => />.
case (r=2) => />. rewrite (consistent_s21_s42 (nth witness ss 2).`2 (nth witness ss 4).`2) => />. rewrite H3 => />.
case (r=3) => />. rewrite (consistent_s10_s43 (nth witness ss 1).`2 (nth witness ss 4).`2) => />. rewrite H3 => />.
case (r=4) => />. rewrite (consistent_s11_s44 (nth witness ss 1).`2 (nth witness ss 4).`2) => />. rewrite H3 => />.
case (r=5) => />. rewrite (consistent_s00_s45 (nth witness ss 0).`2 (nth witness ss 4).`2) => />. rewrite H3 => />.
progress. have : false. smt(). progress.
progress. have : false. smt(). progress. qed.

realize valid_reconstruct.
move => ss H. 
rewrite /valid_secret /reconstruct /valid_rand /reconstruct_rand => />. qed.

realize size_pid_set. rewrite size_iseq => />. qed.
realize valid_public_encoding. move => x. rewrite /valid_shares /public_encoding allP /valid_secret => />. split.
rewrite /init_sh /shr_idx /pid_set !iseq_5 => />. 
move => i. rewrite in_iseq => />Hi1 Hi2. rewrite allP => />j. rewrite in_iseq => />Hj1 Hj2.
rewrite /consistent_shares /get_party_share /pid_set => />.
rewrite !(assoc_iseq_some witness) => />.
rewrite !size_zipl !size_iseq /pshare => />. rewrite !array5_to_list_init => />. rewrite !mkseq_iseq => />. rewrite !iseq_5 => />. rewrite !size_zipl => />. rewrite size_iseq => />. 
rewrite !size_zipl !size_iseq /pshare => />. rewrite !array5_to_list_init => />. rewrite !mkseq_iseq => />. rewrite !iseq_5 => />. rewrite !size_zipl => />. rewrite size_iseq => />. 
rewrite !(nth_onth) !onth_zipl => />. rewrite !(onth_nth witness) => />. rewrite size_iseq => />. rewrite size_iseq => />. 
rewrite consistent_raw_shares_pshare => />. qed.

op init_sh (p : pid, rs : rshr) : shr=
   Array6.of_list witness (map (fun i => rs.[i]) (shr_idx p)).

clone include SSSecurity with
  theory SSS <- MaurerSSS,
  op gen_rand _ = gen_rand,
  op simulator cr r = 
    let i = cr_missing cr in
    let rs = rshare_idx i witness r in
    let ss = Array5.init (fun i => init_sh i rs) in
    map (fun pid => (pid,ss.[pid])) cr
  proof *.
  realize gen_rand_ll. move => p. rewrite gen_rand_ll => />. qed.
  realize simulator_domain. move => cr r. rewrite /simulator => |>.
  rewrite -map_comp /(\o) => |>. rewrite map_id => |>. qed.
  realize valid_gen_rand. move => p r H. rewrite /valid_rand => />. qed.
  realize ss_security.
  proc. simplify.
  transitivity{1}
    { ssc <@ Maurer5SS.SSSecurity.real(s,cr); }
    ( ={cr, s} /\ valid_corrupted_set cr{1} ==> ={ssc} )
    ( ={cr, s} /\ valid_corrupted_set cr{1} ==> ={ssc} ).
    progress. exists cr{2} s{2} => |>. 
    progress.
  inline *. wp. sp. auto => |>. 
  progress. rewrite /corrupted => |>. rewrite list_eq => |>. rewrite !size_map => |>n Hn1 Hn2. rewrite !(nth_map witness) => |>. rewrite /share => |>. rewrite array5_to_list_init => |>. rewrite zipl_zip => |>. rewrite size_mkseq size_pid_set => |>. rewrite assoc_zip => |>. rewrite size_mkseq size_pid_set => |>. have : nth witness cr{2} n \in cr{2}. rewrite nth_in => |>. move => H3. have : nth witness cr{2} n \in iseq 5. move :H. rewrite /valid_corrupted_set => |>V1 V2 V3. rewrite V3 => |>. move => H4. have :  0 <= nth witness cr{2} n < 5. move :H4. rewrite in_iseq => |>. move => H5. rewrite Array5.initE (onth_nth witness) => |>. rewrite size_mkseq !index_iseq => |>. move :H5. progress. rewrite nth_mkseq => |>. rewrite index_iseq => |>. move :H5. progress. rewrite index_iseq => |>. rewrite H5 => |>. 
  transitivity{2}
    { ssc <@ Maurer5SS.SSSecurity.ideal(s,cr); }
    ( ={cr, s} /\ valid_corrupted_set cr{1} ==> ={ssc} )
    ( ={cr, s} /\ valid_corrupted_set cr{1} ==> ={ssc} ).
    progress. exists cr{2} s{2} => |>. 
    progress.
  call ss_security => |>. auto => |>. 
  inline *. wp. sp. auto => |>. qed.

clone import ListSecretSharingScheme as MaurerLSSS with
  theory SS = MaurerSSS
  proof *.
  realize n_gt0. rewrite /n => />. qed.
