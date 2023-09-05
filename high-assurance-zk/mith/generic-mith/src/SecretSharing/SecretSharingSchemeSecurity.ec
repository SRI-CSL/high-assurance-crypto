require import DBool DMap DProd List Distr Int.

from SecretSharing require import ASecretSharingScheme.
from General require import Utils ListExt.

theory SecretSharingSchemeSecurity.

  clone import SecretSharingScheme as SS.

  op valid_corrupted_set (cr : pid_t list) : bool = 
    size cr = t /\ uniq cr /\ (forall pid, pid \in cr => pid \in pid_set).

  type aux_t.

  module type Rand_t = {
    proc gen(aux : aux_t) : rand_t
  }.

  module type Distinguisher_t = {
    proc choose(aux : aux_t) : pid_t list
    proc guess(s : secret_t, ss : shares_t) : bool
  }.

  module type Evaluator_t = {
    proc share(aux : aux_t, r : rand_t, s : secret_t, cr : pid_t list) : shares_t
  }.

  module Game(D : Distinguisher_t, R : Rand_t, E : Evaluator_t) = {
    proc main(aux : aux_t, s : secret_t) : bool = {
      var r, b', ss, cr;

      cr <@ D.choose(aux);
      r <@ R.gen(aux);
      if (valid_rand r ((*secret_public*) s) /\ valid_corrupted_set cr) {
        ss <@ E.share(aux,r,s,cr);
        b' <@ D.guess(s,ss);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  module RealEvaluator = {
    proc share(aux : aux_t, r : rand_t, s : secret_t, cr : pid_t list) : shares_t = {
      var ss, ssc;

      ss <- share r s;
      ssc <- map (fun pid => (pid, oget (assoc ss pid))) cr;

      return ssc;
    }
  }.

  module type Simulator_t = {
    proc simm(aux : aux_t, r : rand_t, cr : pid_t list) : shares_t
  }.

  module IdealEvaluator (S : Simulator_t) = {
    proc share(aux : aux_t, r : rand_t, s : secret_t, cr : pid_t list) : shares_t = {
      var ssc;
      ssc <- S.simm(aux,r,cr);

      return ssc;
    }
  }.

  module GameReal (D : Distinguisher_t) (R : Rand_t) = Game(D,R,RealEvaluator).
  module GameIdeal (D : Distinguisher_t) (R : Rand_t) (S : Simulator_t) = Game(D,R,IdealEvaluator(S)).

end SecretSharingSchemeSecurity.

(*
theory SSSecurity.

  clone import SecretSharingScheme as SSS.

  op valid_corrupted_set (cr : pid_t list) : bool = 
    size cr = t /\ uniq cr /\ (forall pid, pid \in cr => pid \in pid_set).
    
  op gen_rand : public_t -> rand_t distr.
  op simulator : pid_t list -> rand_t -> shares_t.
  
  op corrupted cr (xs: (pid_t * 'a) list) = map (fun pid => (pid, oget (assoc xs pid))) cr.

  module SSSecurity = {
    proc real(cr:pid_t list,s:secret_t) : shares_t = {
      var r,ss,ssc;
      r <$ gen_rand (secret_public s);
      ss <- share r s;
      ssc <- corrupted cr ss;
      return ssc;
    }
    proc ideal(cr:pid_t list,s:secret_t) : shares_t = {
      var r,ssc;
      r <$ gen_rand (secret_public s);
      ssc <- simulator cr r;
      return ssc;
    }
  }.
  
  axiom valid_gen_rand p r :
    r \in gen_rand p => SSS.valid_rand r p.

  axiom gen_rand_ll p :
    is_lossless (gen_rand p).

  axiom simulator_domain cr r :
    unzip1 (simulator cr r) = cr.

  axiom ss_security :
    equiv [SSSecurity.real ~ SSSecurity.ideal : ={cr,s} /\ valid_corrupted_set cr{1} ==> ={res} ].

  section Proofs.

  clone import SecretSharingSchemeSecurity as SSSSec with
    theory SS = SSS.

  declare module D : SSSSec.Distinguisher_t.
  module R : SSSSec.Rand_t = {
    proc gen(aux:aux_t,p) = {
      var r;
      r <$ gen_rand p;
      return r;
    }
  }.
  module S : SSSSec.Simulator_t = {
    proc simm(aux : aux_t, r : rand_t, cr : pid_t list) : shares_t = {
      var ssc;
      ssc <- simulator cr r; 
      return ssc;
    } 
  }.

  local module Security = {
    proc real1 (aux,s,cr) =
    {
      var rs,ss,b';
      if (valid_corrupted_set cr)
      {
        rs <$ gen_rand (secret_public s);
        ss <@ RealEvaluator.share(aux,rs,s,cr);
        b' <@ D.guess(s,ss);
      }
      else { b' <$ {0,1}; }
      return b';
    }
    proc ideal1 (aux,s,cr) =
    {
      var rs,ss,b';
      if (valid_corrupted_set cr)
      {
        rs <$ gen_rand (secret_public s);
        ss <@ IdealEvaluator(S).share(aux,rs,s,cr);
        b' <@ D.guess(s,ss);
      }
      else { b' <$ {0,1}; }
      return b';
    }
  }.

  lemma sss_security :
    equiv [SSSSec.GameReal(D,R).main ~ SSSSec.GameIdeal(D,R,S).main : ={glob D,aux,s} ==> ={res} ].
    proc. simplify. seq 1 1 : (#pre /\ ={cr}).
    call (_:true) => />*. auto => />*.
    inline R.gen. sp. 
    (* if left *)
    transitivity{1}
      { b' <@ Security.real1(aux,s,cr); }
      ( aux0{1}=aux{1} /\ p{1} = SS.secret_public s{1} /\ ={glob D,aux,aux0,s,cr,p} ==> ={b'} )
      ( aux0{1}=aux{1} /\ p{1} = SS.secret_public s{1} /\ ={glob D,aux,aux0,s,cr,p} ==> ={b'} ).
      progress. exists (glob D){2} aux{2} aux{2} cr{2} (SS.secret_public s{2}) s{2} => />*. 
      progress. 
    inline *. wp. sp. if{2}.
    seq 1 1 : (#pre /\ r0{1}=rs{2} /\ SS.valid_rand r0{1} p{1}). auto => |>.
    move => &2 H H0 r H1 H2. rewrite (_:SS.valid_rand=valid_rand). progress. rewrite valid_gen_rand => |>.
    sp. if{1}. sp. call (_: true ) => />*. auto => />*. 
    conseq (_ : false ==> _ ). progress. smt(). auto => />*.
    seq 1 0 : #pre. rnd{1}. auto => />*. rewrite gen_rand_ll => />*. 
    sp. if{1}. sp. conseq (_ : false ==> _). progress. smt(). auto => />*. 
    auto => />*. 
    (* if right *)
    transitivity{2}
      { b' <@ Security.ideal1(aux,s,cr); }
      ( aux0{1}=aux{1} /\ p{1} = SS.secret_public s{1} /\ ={glob D,aux,aux0,s,cr,p} ==> ={b'} )
      ( aux0{1}=aux{1} /\ p{1} = SS.secret_public s{1} /\ ={glob D,aux,aux0,s,cr,p} ==> ={b'} ).
      progress. exists (glob D){2} aux0{2} aux0{2} cr{2} (SS.secret_public s{2}) s{2} => />*. 
      progress. 
    inline Security.real1 Security.ideal1. sp. if. 
      progress.
    wp. seq 2 2 : ( ={glob D,s0,ss0} ).
    inline RealEvaluator.share IdealEvaluator(S).share S.simm. 
    transitivity{1}
      { ss0 <@ SSSecurity.real(cr,s); }
      ( valid_corrupted_set cr{1} /\ p{1} = SS.secret_public s{1} /\ aux0{1}=aux{1} /\ aux1{1}=aux{1} /\ s0{1}=s{1} /\ cr0{1}=cr{1} /\ ={glob D,aux,aux0,aux1,s,s0,cr,cr0,p} ==> ={glob D,s0,ss0,p} )
      ( valid_corrupted_set cr{1} /\ p{1} = SS.secret_public s{1} /\ aux0{1}=aux{1} /\ aux1{1}=aux{1} /\ s0{1}=s{1} /\ cr0{1}=cr{1} /\ ={glob D,aux,aux0,aux1,s,s0,cr,cr0,p} ==> ={glob D,s0,ss0,p} ).
      progress. exists (glob D){2} aux0{2} aux0{2} aux0{2} cr{2} cr{2} (SS.secret_public s{2}) s{2} s{2} => />*.
      progress.
    inline SSSecurity.real. sp. wp. rnd => />. progress.
    transitivity{2}
      { ss0 <@ SSSecurity.ideal(cr,s); }
      ( valid_corrupted_set cr{1} /\ p{1} = SS.secret_public s{1} /\ aux0{1}=aux{1} /\ aux1{1}=aux{1} /\ s0{1}=s{1} /\ cr0{1}=cr{1} /\ ={glob D,aux,aux0,aux1,s,s0,cr,cr0,p} ==> ={glob D,s0,ss0,p} )
      ( valid_corrupted_set cr{1} /\ p{1} = SS.secret_public s{1} /\ aux0{1}=aux{1} /\ aux1{1}=aux{1} /\ s0{1}=s{1} /\ cr0{1}=cr{1} /\ ={glob D,aux,aux0,aux1,s,s0,cr,cr0,p} ==> ={glob D,s0,ss0,p} ).
      progress. exists (glob D){2} aux1{2} aux1{2} aux1{2} cr0{2} cr0{2} (SS.secret_public s0{2}) s0{2} s0{2} => />*.
      progress.
    call ss_security => />*. auto => />. 
    inline SSSecurity.ideal. sp. wp. rnd => />*. auto => />*. 
    call (_:true) => />*. auto => />*.
    wp. rnd => />*. auto => />*. 
    inline *. sp. wp. if{1}.
    seq 1 1 : (#pre /\ rs{1}=r0{2} /\ SS.valid_rand rs{1} p{1}). rnd => |>. auto => |>.
    move => &1 &2 H H0 r H1 H2. rewrite (_:SS.valid_rand=valid_rand). progress. rewrite valid_gen_rand => |>.
    auto => |>. move => &2 H H0 r H1 H2. rewrite (_:SS.valid_rand=valid_rand). progress. rewrite valid_gen_rand => |>.
    sp. if{2}. sp. call (_:true) => />*. auto => />*. 
    conseq (_: false ==> _). rewrite /valid_rand => />*. smt(). auto => />*.
    seq 0 1 : #pre. rnd{2} => />*. auto => />*. rewrite gen_rand_ll => />*.
    sp. if{2}. sp. conseq (_:false ==> _). rewrite /valid_rand => />*. smt(). auto => />*.
    rnd => />*. auto => />*. qed.

  end section Proofs.

end SSSecurity.

theory ListSSSecurity.

  clone import SSSecurity as SSSec.
  clone import ListSecretSharingScheme as LSS with
    theory SS = SSSec.SSS.

  clone import ProdSampling as DPS with
    type t1 = SS.rand_t,
    type t2 = SS.rand_t list.

  clone import DMapSampling as DMPS with
    type t1 = (SS.rand_t * SS.rand_t list),
    type t2 = SS.rand_t list.

  op lshare cr rs ss = to_pids_t cr (map (fun r_s => let (r,s) = r_s in SS.share r s) (zip rs ss)).
  op lsimulator cr r = to_pids_t cr (map (SSSec.simulator cr) r).

  module LSec = {
    proc lgen (xs) = {
      var rs;
      rs <$ djoinmap SSSec.gen_rand (map SS.secret_public xs);
      return rs;
    }
    proc gen_cons(x:SS.secret_t,l:SS.secret_t list) = {
      var r1,r2;
      r1 <$ SSSec.gen_rand (SS.secret_public x);
      r2 <@ lgen(l);
      return (r1 :: r2);
    }
    proc lreal(cr,s) = {
      var r;
      r <@ lgen (s);
      return (lshare cr r s);
    }
    proc lideal(cr,s) = {
      var r;
      r <@ lgen (s);
      return (lsimulator cr r);
    }
  }.

  lemma gen_cons_equiv :
    equiv [ LSec.gen_cons ~ LSec.lgen : x{1}::l{1}=xs{2} ==> ={res} ].
    proc. simplify. 
    alias{1} 2 t = 0. swap{1} 2 1. alias{1} 3 r12 = (r1,r2).
    transitivity{1}
      { r12 <@ DPS.S.sample(gen_rand (SS.secret_public x),djoinmap gen_rand (map SS.secret_public l)); }
      ( ={x,l} ==> ={x,l,r12} /\ r12{1} = (r1{1},r2{1}) )
      ( cons x{1} l{1} = xs{2} ==> cons r12{1}.`1 r12{1}.`2 = rs{2} ).
      progress. exists l{1} x{1} => |>.
      progress. 
    transitivity{2}
      { r12 <@ DPS.S.sample2(gen_rand (SS.secret_public x),djoinmap gen_rand (map SS.secret_public l)); }
      ( ={x,l} ==> ={x,l,r12} /\ r12{1} = (r1{1}, r2{1}) )
      ( ={x,l} ==> ={x,l,r12} ).
      progress. exists l{2} x{2} => |>.
      progress.
    inline *. wp. sp. auto => |>. 
    symmetry. call DPS.sample_sample2 => |>. auto => |>.
    inline *. wp. sp. 
    alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 rs = uncurry cons r.
    transitivity{1}
      { rs <@ DMPS.S.map(d1 `*` d2,uncurry cons); }
      ( ={d1,d2,x,l} ==> ={d1,d2,x,l,rs} /\ rs{1}=cons r{1}.`1 r{1}.`2 )
      ( d1{1} = gen_rand (SS.secret_public x{1}) /\ d2{1} = djoinmap gen_rand (map SS.secret_public l{1}) /\ cons x{1} l{1} = xs{2} ==> ={rs} ).
      progress. exists (gen_rand (SS.secret_public x{1})) (djoinmap gen_rand (map SS.secret_public l{1})) l{1} x{1} => |>. 
      progress.
    inline *. wp. auto => |>.
    transitivity{1}
      { rs <@ DMPS.S.sample(d1 `*` d2,uncurry cons); }
      ( ={d1,d2,x,l} ==> ={d1,d2,x,l,rs} )
      ( d1{1} = gen_rand (SS.secret_public x{1}) /\ d2{1} = djoinmap gen_rand (map SS.secret_public l{1}) /\ cons x{1} l{1} = xs{2} ==> ={rs} ).
      progress. exists (gen_rand (SS.secret_public x{1})) (djoinmap gen_rand (map SS.secret_public l{1})) l{1} x{1} => |>. 
      progress. 
    symmetry. call DMPS.sample => |>. auto => |>. 
    inline *. swap{1} 2 -1. sp. wp. rnd => |>. auto => |>. 
    move => &1. split.
    move => rs H. rewrite djoin_cons => |>. 
    move => H r0 H0. rewrite djoin_cons => |>. qed.

  lemma lss_security S :
    equiv [ LSec.lreal ~ LSec.lideal : s{1}=S /\ ={cr,s} /\ valid_corrupted_set cr{1} ==> ={res} ].
    elim S => |>. 
    (* nil *)
    proc. simplify. inline *. sp. wp. rnd => |>. progress.
    move :H1 H2. rewrite !djoin_nil supp_dunit => />.
    auto => |>. progress. move :H0. rewrite !djoin_nil supp_dunit => />.
    (* cons *)
    move => X L H. proc. simplify. 
    (* change left rand *)
    transitivity{1}
      { r <@ LSec.gen_cons(X,L); }
      ( cons X L = s{2} /\ ={cr,s} /\ valid_corrupted_set cr{1} ==> ={r,cr,s} )
      ( cons X L = s{2} /\ ={cr,s} /\ valid_corrupted_set cr{1} ==> ={cr,s} /\ lshare cr{1} r{1} s{1} = lsimulator cr{2} r{2} ).
      progress. exists cr{2} (cons X L) => |>. 
      progress. 
    symmetry. call gen_cons_equiv => |>. auto => |>.
    (* change right rand *)
    transitivity{2}
      { r <@ LSec.gen_cons(X,L); }
      ( cons X L = s{2} /\ ={cr,s} /\ valid_corrupted_set cr{1} ==> ={cr,s} /\ lshare cr{1} r{1} s{1} = lsimulator cr{2} r{2} )
      ( cons X L = s{2} /\ ={cr,s} /\ valid_corrupted_set cr{1} ==> ={r,cr,s} ).
      progress. exists cr{2} (cons X L) => |>. 
      progress. 
    (* actual proof *)
    inline LSec.gen_cons. sp.
    alias{1} 2 v = SSSec.corrupted cr (SS.share r1 X).
    alias{2} 2 v = SSSec.simulator cr r1.
    seq 2 2 : (#pre /\ ={v} /\ v{1} = SSSec.corrupted cr{1} (SS.share r1{1} X) /\ v{2} = SSSec.simulator cr{2} r1{2} ).
    (* head proof *)
    transitivity{1}
      { v <@ SSSec.SSSecurity.real(cr,x); }
      ( X=x{1} /\ L=l{1} /\ ={x,l,cr,s} ==> ={x,l,cr,s,v} /\ v{1} = corrupted cr{1} (SS.share r1{1} x{1}) )
      ( x{2} = X /\ l{2} = L /\ x{1} = X /\ l{1} = L /\ cons X L = s{2} /\ ={cr, s} /\ valid_corrupted_set cr{1} ==> (x{2} = X /\ l{2} = L /\ x{1} = X /\ l{1} = L /\ cons X L = s{2} /\ ={cr, s} /\ valid_corrupted_set cr{1}) /\ ={v} /\ v{2} = simulator cr{2} r1{2} ).
      progress. exists cr{2} l{2} (cons x{2} l{2}) x{2} => |>.
      progress. 
    inline *. wp. sp. rnd => |>. auto => |>.
    transitivity{2}
      { v <@ SSSec.SSSecurity.ideal(cr,x); }
      ( x{2} = X /\ l{2} = L /\ x{1} = X /\ l{1} = L /\ cons X L = s{2} /\ ={cr, s} /\ valid_corrupted_set cr{1} ==> (x{2} = X /\ l{2} = L /\ x{1} = X /\ l{1} = L /\ cons X L = s{2} /\ ={cr, s} /\ valid_corrupted_set cr{1}) /\ ={v} )
      ( X=x{1} /\ L=l{1} /\ ={x,l,cr,s} ==> ={x,l,cr,s,v} /\ v{2} = simulator cr{2} r1{2} ).
      progress. exists cr{2} l{2} (cons x{2} l{2}) x{2} => |>.
      progress. 
    call SSSec.ss_security => |>. auto => |>.
    inline *. wp. sp. rnd => |>. auto => |>.
    wp. 
    (* head + tail proof *)
    conseq (_: (x{2} = X /\ l{2} = L /\ x{1} = X /\ l{1} = L /\ cons X L = s{2} /\ ={cr, s} /\ valid_corrupted_set cr{1}) ==> ={cr,s} /\ lshare cr{1} r2{1} L = lsimulator cr{2} r2{2} ).
    progress.
    progress. move :H1 H2. rewrite /lshare /lsimulator /corrupted /to_pids_t !list_eq => |>. rewrite !size_map => |>H1 H2 H3 n Hn1 Hn2.
    have : nth witness (map (fun (pid : SSS.pid_t) => (pid, oget (assoc (SS.share r1{1} x{2}) pid))) cr{2}) n = nth witness (simulator cr{2} r1{2}) n. rewrite H2 => />. clear H2.
    have : nth witness  (map (fun (pid : SS.pid_t) => (pid,  map (SS.get_party_share pid) (map (fun (r_s : SSS.rand_t * SSS.secret_t) => let (r, s) = r_s in SS.share r s) (zip r2_L l{2})))) cr{2}) n = nth witness (map (fun (pid : SS.pid_t) => (pid, map (SS.get_party_share pid) (map (simulator cr{2}) r2_R))) cr{2}) n. rewrite H3 => />. clear H3.
    rewrite !(nth_map witness) => />. rewrite -!map_comp /(\o) => />. rewrite !list_eq => />. rewrite !size_map !size_zip => />. move => H2 H3. rewrite (prod_id (nth witness (simulator cr{2} r1{2}) n)) => |>H4 H5. 
    rewrite /get_party_share => |>. rewrite H5 => |>. rewrite H4 => |>. rewrite assoc_nth_some => />. rewrite -H1 => />. move :H0. rewrite /valid_corrupted_set => />H6 H7 H8. rewrite SSSec.simulator_domain => |>.  
    (* tail proof *)
    alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 vs = lshare cr r2 L.
    alias{2} 1 t = 0. swap{2} 1 1. alias{2} 2 vs = lsimulator cr r2.
    transitivity{1}
      { vs <@ LSec.lreal(cr,L); }
      ( l{1}=L /\ x{1}=X /\ ={x,l,cr,s} ==> ={x,l,cr,s,vs} /\ vs{1} = lshare cr{1} r2{1} L )
      ( x{2} = X /\ l{2} = L /\ x{1} = X /\ l{1} = L /\ cons X L = s{2} /\ ={cr,s} /\ valid_corrupted_set cr{1} ==> ={cr,s} /\ vs{1} = lsimulator cr{2} r2{2} ).
      progress. exists cr{2} l{2} (cons x{2} l{2}) x{2} => |>. 
      progress.
    inline *. wp. sp. auto => |>. 
    transitivity{2}
      { vs <@ LSec.lideal(cr,L); }
      ( x{2} = X /\ l{2} = L /\ x{1} = X /\ l{1} = L /\ cons X L = s{2} /\ ={cr, s} /\ valid_corrupted_set cr{1} ==> ={cr,s,vs} )
      ( l{1}=L /\ x{1}=X /\ ={x,l,cr,s} ==> ={x,l,cr,s,vs} /\ vs{2} = lsimulator cr{2} r2{2} ).
      progress. exists cr{2} l{2} (cons x{2} l{2}) x{2} => |>. 
      progress.
    call H => |>. auto => |>.
    inline *. wp. sp. auto => |>.
    (* end *)
    call gen_cons_equiv => |>. auto => |>. qed.
  
  clone include SSSecurity with
    theory SSS = LSS,
    op gen_rand ps = djoinmap SSSec.gen_rand ps,
    op simulator cr r = to_pids_t cr (map (SSSec.simulator cr) r)
    proof *.
    realize ss_security.
    proc. simplify.
    transitivity{1}
      { ssc <@ LSec.lreal(cr,s); }
      ( ={cr, s} /\ ListSSSecurity.valid_corrupted_set cr{1} ==> ={ssc} )
      ( ={cr, s} /\ ListSSSecurity.valid_corrupted_set cr{1} ==> ={ssc} ).
      progress. exists cr{2} s{2} => |>. 
      progress.
    inline *. wp. sp. auto => |>.
    progress. rewrite /corrupted /share /lshare /to_pids_t list_eq => |>. rewrite !size_map => |>. move => n Hn1 Hn2. rewrite !(nth_map witness) => |>. rewrite -!map_comp /(\o) => |>. rewrite assoc_map_r => |>. move :H. rewrite /valid_corrupted_set => |>V1 V2 V3. rewrite V3 => |>. rewrite nth_in => |>. rewrite -!map_comp /(\o) => |>. 
    transitivity{2}
      { ssc <@ LSec.lideal(cr,s); }
      ( ={cr, s} /\ ListSSSecurity.valid_corrupted_set cr{1} ==> ={ssc} )
      ( ={cr, s} /\ ListSSSecurity.valid_corrupted_set cr{1} ==> ={ssc} ).
      progress. exists cr{2} s{2} => |>. 
      progress.
    exists* s{1}. elim*. move => S. call (lss_security S) => |>. auto => |>.
    inline *. wp. sp. auto => |>. qed.
    realize simulator_domain.
    move => cr r. rewrite /simulator /to_pids_t => |>. rewrite -!map_comp /(\o) => |>. rewrite map_id => |>. qed.
    realize gen_rand_ll.
    move => p. rewrite /gen_rand => />. rewrite djoin_ll => />d. rewrite in_nth => />i. 
    rewrite size_map => />Hi1 Hi2. rewrite !(nth_map witness) => |>. rewrite SSSec.gen_rand_ll => />. qed.
    realize valid_gen_rand.
    move => p r. rewrite /gen_rand /valid_rand => |>. rewrite supp_djoinmap !allP => |>H H0. 
    rewrite H => />x H1. rewrite SSSec.valid_gen_rand => |>.
    pose y := (x.`2,x.`1). have : y.`2 \in gen_rand y.`1. rewrite H0 => />. move :H1. rewrite /t !in_nth => />i. rewrite !size_zip => />Hi1 Hi2. exists i => />. rewrite /y !nth_onth !(onth_nth (witness,witness)) => />. rewrite size_zip => />. rewrite size_zip => />. smt(). rewrite !nth_zip => />. rewrite H => />. smt(). rewrite /y => />. qed.
  
end ListSSSecurity.
*)
