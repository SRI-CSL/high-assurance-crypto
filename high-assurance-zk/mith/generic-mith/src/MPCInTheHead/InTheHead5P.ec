require import Int IntDiv Real Distr List.

from General require import ListExt Utils.
from Functionalities require import AProtocolFunctionality.
from SecretSharing require import ASecretSharingScheme SecretSharingSchemeSecurity.
from MPC require import AProtocol ProtocolPrivacy.
from Commitment require import ACommitmentScheme Binding Hiding.
from ZeroKnowledge require import AZKPProtocol Completeness Soundness ZeroKnowledge.
from MPCInTheHead require import InTheHead.

theory InTheHead5P.

  type witness_t.
  type instance_t.

  type pid_t = pid_mpc_t.
  op pid_set = pid_mpc_set.

  clone import SecretSharingScheme as SS5 with
    op n = 5, op t = 2, type pid_t = pid_t, op pid_set = pid_set, type secret_t = witness_t,
    op get_party_share pid xs = oget (assoc xs pid)
  proof n_pos, t_pos, pid_set_size, pid_set_uniq.
  realize n_pos by done.  
  realize t_pos by done.  
  realize pid_set_size by done.  
  realize pid_set_uniq by done.

  clone import InTheHead as InTheHead5P with 
    theory SS = SS5, op MPC.ProtocolFunctionality.t = SS5.t, type witness_t = witness_t, type instance_t = instance_t, op MPC.ProtocolFunctionality.valid_inputs (c : ProtocolFunctionality.circuit_t) (xs : inputs_t) = 
      unzip1 xs = SS5.pid_set /\
      exists r x, valid_rand r x /\ valid_secret x /\ share r x = map (fun pid => (pid, sinput pid xs)) SS5.pid_set.
  import MPC.
  import ProtocolFunctionality.
  import CS.

  clone import Hiding with 
    theory CommitmentScheme <- CS,
    type aux_t = (witness_t * statement_t) * pid_t * bool,
    op valid_query x = let (m1,m2,aux) = x in 
                       let (wx,pid,b) = aux in b.
  clone import Privacy with theory Protocol <- MPC, type aux_t = instance_t, type env_input_t = secret_t.
  clone import SecretSharingSchemeSecurity with theory SS = SS5, type aux_t = statement_t.
  clone import ZeroKnowledge with theory ZKPProtocol = InTheHead.

  section ZeroKnowledge.
    module type PCSRand_t = { proc gen() : CS.rand_t }.

    module AllCSRand (RCS1 : PCSRand_t, RCS2 : PCSRand_t, RCS3 : PCSRand_t,
                    RCS4 : PCSRand_t, RCS5 : PCSRand_t) = {
      proc gen(aux : Hiding.aux_t) : CS.rand_t = {
        var r;

        if (aux.`2 = P1) { r <@ RCS1.gen(); }
        if (aux.`2 = P2) { r <@ RCS2.gen(); }
        if (aux.`2 = P3) { r <@ RCS3.gen(); }
        if (aux.`2 = P4) { r <@ RCS4.gen(); }
        if (aux.`2 = P5) { r <@ RCS5.gen(); }

        return r;

      }
    }.

    lemma csrandp_ll (RCS1 <: PCSRand_t) (RCS2 <: PCSRand_t{RCS1}) 
                     (RCS3 <: PCSRand_t{RCS1,RCS2}) (RCS4 <: PCSRand_t{RCS1,RCS2,RCS3}) 
                     (RCS5 <: PCSRand_t{RCS1,RCS2,RCS3,RCS4}) : 
      islossless RCS1.gen =>
      islossless RCS2.gen =>
      islossless RCS3.gen =>
      islossless RCS4.gen =>
      islossless RCS5.gen =>
      islossless AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5).gen.
    proof. by progress; proc; islossless. qed.

    lemma csrandp_equiv (RCS1 <: PCSRand_t) (RCS2 <: PCSRand_t{RCS1}) 
                        (RCS3 <: PCSRand_t{RCS1,RCS2})
                    (RCS4 <: PCSRand_t{RCS1,RCS2,RCS3}) (RCS5 <: PCSRand_t{RCS1,RCS2,RCS3,RCS4}) : 
      equiv [ AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5).gen ~ 
              AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5).gen : ={glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5} /\ aux{1}.`2 = aux{2}.`2 ==> ={res} /\ ={glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5} ].
    proof. 
      proc.
      if => //; first by smt(). 
        seq 1 1 : (#pre /\ ={r}); first by call (_ : true).
        (if; first by smt()); first by exfalso => /#.
        (if; first by smt()); first by exfalso => /#.
        (if; first by smt()); first by exfalso => /#.
        (if; first by smt()); first by exfalso => /#.
        by done. 
      (if; first by smt()). 
        seq 1 1 : (#pre /\ ={r}); first by call (_ : true).
        (if; first by smt()); first by exfalso => /#.
        (if; first by smt()); first by exfalso => /#.
        (if; first by smt()); first by exfalso => /#.
        by done. 
      (if; first by smt()). 
        seq 1 1 : (#pre /\ ={r}); first by call (_ : true).
        (if; first by smt()); first by exfalso => /#.
        (if; first by smt()); first by exfalso => /#.
        by done. 
      (if; first by smt()). 
        seq 1 1 : (#pre /\ ={r}); first by call (_ : true).
        (if; first by smt()); first by exfalso => /#.
        by done. 
      (if; first by smt()); first by call (_ : true).  
      by exfalso => /#.
    qed.

    module RP (RSS : SecretSharingSchemeSecurity.Rand_t, RMPC : Privacy.Rand_t,
               RCS1 : PCSRand_t, RCS2 : PCSRand_t, RCS3 : PCSRand_t,
               RCS4 : PCSRand_t, RCS5 : PCSRand_t) = {

      var i, j, k, l, m : pid_t
      var rcsi, rcsj, rcsk, rcsl, rcsm : CS.rand_t

      module AllCSRand = AllCSRand(RCS1,RCS2,RCS3,RCS4,RCS5)

      proc gen(xp : prover_input_t) : prover_rand_t = {
        var rss, rmpc;
        var w, x, ws;

        (w,x) <- xp;
        (i,j) <$ InTheHead5P.challenge_distr;
        (k,l,m) <- get_other_pids i j;

        rss <@ RSS.gen(x);
        ws <- share rss w;
        rmpc <@ RMPC.gen(relc, [i;j], x);
        rcsi <@ AllCSRand.gen(xp,i,true);
        rcsj <@ AllCSRand.gen(xp,j,true);
        rcsk <@ AllCSRand.gen(xp,k,true);
        rcsl <@ AllCSRand.gen(xp,l,true);
        rcsm <@ AllCSRand.gen(xp,m,true);

        return (rss, rmpc, tuple5_to_list (assemble (i,rcsi) (j,rcsj) (k,rcsk) (l,rcsl) (m,rcsm)));
      }

    }.

    module RealEvaluator0 (MV : MVerifier_t) = {

      proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : (verifier_state_t * InTheHead5P.trace_t) option = {
        var r, c, ch, resp;
        var r_ss, r_mpc, rcs;
        var ws, x_mpc, tr, y;
        var cvs, vs, acceptance;

        (r_ss, r_mpc, rcs) <- rp;

        ws <- SS5.share r_ss w;

        x_mpc <- mk_inputs x ws; (*map (fun pid => (pid, (x,oget (assoc ws pid)))) pid_set;*)
        (tr,y) <- MPC.protocol relc r_mpc x_mpc;

        vs <- map (fun pid => (pid, ((input pid x_mpc, rand pid r_mpc, trace pid tr)))) pid_set;
        cvs <- map (fun pid => 
                    let r_c = oget (assoc rcs pid) in
                    let ysv = oget (assoc vs pid) in 
                    (pid, (ysv, commit r_c ysv))) pid_set;
        c <- map (fun pid => (pid, fst (snd (oget (assoc cvs pid))))) pid_set;

        ch <@ MV.challenge(x, c);
        resp <- InTheHead5P.response cvs ch;

        acceptance <- InTheHead5P.check (x,c,ch) resp;

        r <- Some ((x, c, ch), ((c, ch, resp)));

        return r;
      }
    }.

    module RealEvaluator1 (MV : MVerifier_t) = {

      proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : (verifier_state_t * InTheHead5P.trace_t) option = {
        var r, c, ch, resp;
        var r_ss, r_mpc, rcs;
        var ws, x_mpc, tr, y;
        var cvs, vs, acceptance, bad;

        (r_ss, r_mpc, rcs) <- rp;

        ws <- SS5.share r_ss w;

        x_mpc <- mk_inputs x ws; (*map (fun pid => (pid, (x,oget (assoc ws pid)))) pid_set;*)
        (tr,y) <- MPC.protocol relc r_mpc x_mpc;

        vs <- map (fun pid => (pid, ((input pid x_mpc, rand pid r_mpc, (trace pid tr))))) pid_set;
        cvs <- map (fun pid => 
                    let r_c = oget (assoc rcs pid) in
                    let ysv = oget (assoc vs pid) in 
                    (pid, (ysv, commit r_c ysv))) pid_set;
        c <- map (fun pid => (pid, fst (snd (oget (assoc cvs pid))))) pid_set;

        ch <@ MV.challenge(x, c);
        r <- None;
        bad <- ch <> (RP.i, RP.j);
        if (!bad) {
          resp <- InTheHead5P.response cvs ch;
          acceptance <- InTheHead5P.check (x,c,ch) resp;
          r <- Some ((x, c, ch), ((c, ch, resp)));
        }

        return r;
      }
    }.

    module RealEvaluator2 (MV : MVerifier_t) = {

      proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : (verifier_state_t * InTheHead5P.trace_t) option = {
        var r, c, ch, resp;
        var r_ss, r_mpc, rcs;
        var ws, x_mpc, tr, y;
        var cvs, vs, acceptance, bad;

        (r_ss, r_mpc, rcs) <- rp;

        ws <- SS5.share r_ss w;

        x_mpc <- mk_inputs x ws; (*map (fun pid => (pid, (x,oget (assoc ws pid)))) pid_set;*)
        (tr,y) <- MPC.protocol relc r_mpc x_mpc;

        vs <- map (fun pid => (pid, if pid = RP.k then (witness, witness, witness)
                                    else ((input pid x_mpc, rand pid r_mpc, trace pid tr)))) pid_set;
        cvs <- map (fun pid => 
                    let r_c = oget (assoc rcs pid) in
                    let ysv = oget (assoc vs pid) in 
                    (pid, (ysv, commit r_c ysv))) pid_set;
        c <- map (fun pid => (pid, fst (snd (oget (assoc cvs pid))))) pid_set;
        c <- map (fun pid => (pid, fst (snd (oget (assoc cvs pid))))) pid_set;

        ch <@ MV.challenge(x, c);
        r <- None;
        bad <- ch <> (RP.i, RP.j);
        if (!bad) {
          resp <- InTheHead5P.response cvs ch;
          acceptance <- InTheHead5P.check (x,c,ch) resp;
          r <- Some ((x, c, ch), ((c, ch, resp)));
        }

        return r;
      }
    }.

    module B (D : Distinguisher_t) (RSS : SecretSharingSchemeSecurity.Rand_t, RMPC : Privacy.Rand_t,
              RCS1 : PCSRand_t, RCS2 : PCSRand_t, RCS3 : PCSRand_t,
               RCS4 : PCSRand_t, RCS5 : PCSRand_t, MV : MVerifier_t) = {

      module AllCSRand = AllCSRand(RCS1,RCS2,RCS3,RCS4,RCS5)

      var w : witness_t
      var x : statement_t
      var i, j, k, l, m : pid_mpc_t
      var vs : views_t
      var rcsi, rcsj : CS.rand_t

      proc choose(aux : Hiding.aux_t) : msg_t * msg_t * Hiding.aux_t  = {
        var ws, x_mpc, tr, y;
        var r, rss, rmpc, dummy, wx, good;
    
        (wx,dummy,good) <- aux;
        (w,x) <- wx;

        rss <@ RSS.gen(x);
        r <- (witness,witness,(witness,witness,false));

        if (SS5.valid_rand rss w) {

          ws <- SS5.share rss w;
          (i,j) <$ InTheHead5P.challenge_distr;
          (k,l,m) <- get_other_pids i j;

          rmpc <@ RMPC.gen(relc, [i;j], x);

          rcsi <@ AllCSRand.gen(wx,i,true);
          rcsj <@ AllCSRand.gen(wx,j,true);

          if (valid_rands relc rmpc /\ valid_rand rcsi /\ valid_rand rcsj) {

            x_mpc <- mk_inputs x ws; (*map (fun pid => (pid, (x,oget (assoc ws pid)))) pid_set;*)
            (tr,y) <- MPC.protocol relc rmpc x_mpc;

            vs <- map (fun pid => (pid, if pid = k then (witness, witness, witness)
                                        else ((input pid x_mpc, rand pid rmpc, trace pid tr)))) pid_set;

            r <- ((witness, witness, witness), 
                  ((input k x_mpc, rand k rmpc, trace k tr)), (aux.`1, k, true));
            }
          }

        return r;
      }

      proc guess(fc : CS.commitment_t) : bool = {
        var resp;
        var ch, ci, cj, r;
        var rcsl, rcsm, cl, cm, c, cvs, acceptance, b, bad;

        rcsl <@ AllCSRand.gen((w,x),l,true);
        rcsm <@ AllCSRand.gen((w,x),m,true);
        if (valid_rand rcsl /\ valid_rand rcsm) {
          ci <- CS.commit rcsi (oget (assoc vs i));
          cj <- CS.commit rcsj (oget (assoc vs j));
          cl <- CS.commit rcsl (oget (assoc vs l));
          cm <- CS.commit rcsm (oget (assoc vs m));

          cvs <- tuple5_to_list (assemble (i, (oget (assoc vs i), ci)) 
                                          (j, (oget (assoc vs j), cj))
                                          (k, (oget (assoc vs k), (fc, witness)))
                                          (l, (oget (assoc vs l), cl))
                                          (m, (oget (assoc vs m), cm)));

          c <- tuple5_to_list (assemble (i, fst ci) (j, fst cj) (k, fc) (l, fst cl) (m, fst cm));
          ch <@ MV.challenge(x, c);

          bad <- ch <> (B.i, B.j);
          if (!bad) {
            resp <- InTheHead5P.response cvs ch;
            acceptance <- InTheHead5P.check (x,c,ch) resp;
            r <- ((x, c, ch), ((c, ch, resp)));
            b <@ D.guess(w, x, Some r);
          } else { b <@ D.guess(w, x, None); }
        }
        else { b <${0,1}; }

        return b;
      }
    }.

    module RealEvaluator3 (MV : MVerifier_t) = {

      proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : (verifier_state_t * InTheHead5P.trace_t) option = {
        var r, c, ch, resp;
        var r_ss, r_mpc, rcs;
        var ws, x_mpc, tr, y;
        var cvs, vs, acceptance, bad;

        (r_ss, r_mpc, rcs) <- rp;

        ws <- SS5.share r_ss w;

        x_mpc <- mk_inputs x ws; (*map (fun pid => (pid, (x,oget (assoc ws pid)))) pid_set;*)
        (tr,y) <- MPC.protocol relc r_mpc x_mpc;

        vs <- map (fun pid => (pid, if pid = RP.k \/ pid = RP.l then (witness, witness, witness)
                                    else (((input pid x_mpc, rand pid r_mpc, trace pid tr))))) pid_set;
        cvs <- map (fun pid => 
                    let r_c = oget (assoc rcs pid) in
                    let ysv = oget (assoc vs pid) in 
                    (pid, (ysv, commit r_c ysv))) pid_set;
        c <- map (fun pid => (pid, fst (snd (oget (assoc cvs pid))))) pid_set;

        ch <@ MV.challenge(x, c);
        r <- None;
        bad <- ch <> (RP.i, RP.j);
        if (!bad) {
          resp <- InTheHead5P.response cvs ch;
          acceptance <- InTheHead5P.check (x,c,ch) resp;
          r <- Some ((x, c, ch), ((c, ch, resp)));
        }

        return r;
      }
    }.

    module C (D : Distinguisher_t) (RSS : SecretSharingSchemeSecurity.Rand_t, RMPC : Privacy.Rand_t,
              RCS1 : PCSRand_t, RCS2 : PCSRand_t, RCS3 : PCSRand_t,
               RCS4 : PCSRand_t, RCS5 : PCSRand_t, MV : MVerifier_t) = {

      module AllCSRand = AllCSRand(RCS1,RCS2,RCS3,RCS4,RCS5)

      var w : witness_t
      var x : statement_t
      var i, j, k, l, m : pid_mpc_t
      var vs : views_t
      var rcsi, rcsj, rcsk : CS.rand_t

      proc choose(aux : Hiding.aux_t) : msg_t * msg_t * Hiding.aux_t = {
        var ws, x_mpc, tr, y;
        var r, rss, rmpc, dummy, wx, good;
    
        (wx,dummy,good) <- aux;
        (w,x) <- wx;

        rss <@ RSS.gen(x);
        r <- (witness,witness,(witness,witness,false));

        if (SS5.valid_rand rss w) {

          ws <- SS5.share rss w;
          (i,j) <$ InTheHead5P.challenge_distr;
          (k,l,m) <- get_other_pids i j;

          rmpc <@ RMPC.gen(relc, [i;j], x);

          rcsi <@ AllCSRand.gen(wx,i,true);
          rcsj <@ AllCSRand.gen(wx,j,true);
          rcsk <@ AllCSRand.gen(wx,k,true);

          if (valid_rands relc rmpc /\ valid_rand rcsi /\ valid_rand rcsj /\ valid_rand rcsk) {

            x_mpc <- mk_inputs x ws; (*map (fun pid => (pid, (x,oget (assoc ws pid)))) pid_set;*)
            (tr,y) <- MPC.protocol relc rmpc x_mpc;

            vs <- map (fun pid => (pid, if pid = k \/ pid = l then (witness, witness, witness)
                                        else ((input pid x_mpc, rand pid rmpc, trace pid tr)))) pid_set;

            r <- ((witness, witness, witness), 
                  ((input l x_mpc, rand l rmpc, trace l tr)), (aux.`1, l, true));
            }
          }

        return r;
      }

      proc guess(fc : CS.commitment_t) : bool = {
        var resp;
        var ch, ci, cj, r;
        var rcsm, ck, cm, c, cvs, acceptance, b, bad;

        rcsm <@ AllCSRand.gen((w,x),m,true);

        if (valid_rand rcsm) {
          ci <- CS.commit rcsi (oget (assoc vs i));
          cj <- CS.commit rcsj (oget (assoc vs j));
          ck <- CS.commit rcsk (oget (assoc vs k));
          cm <- CS.commit rcsm (oget (assoc vs m));

          cvs <- tuple5_to_list (assemble (i, (oget (assoc vs i), ci)) 
                                          (j, (oget (assoc vs j), cj))
                                          (k, (oget (assoc vs k), ck))
                                          (l, (oget (assoc vs l), (fc,witness)))
                                          (m, (oget (assoc vs m), cm)));

          c <- tuple5_to_list (assemble (i, fst ci) (j, fst cj) (k, fst ck) (l, fc) (m, fst cm));
          ch <@ MV.challenge(x, c);

          bad <- ch <> (C.i, C.j);
          if (!bad) {
            resp <- InTheHead5P.response cvs ch;
            acceptance <- InTheHead5P.check (x,c,ch) resp;
            r <- ((x, c, ch), ((c, ch, resp)));
            b <@ D.guess(w,x, Some r);
          } else { b <@ D.guess(w, x, None); }
        }
        else { b <${0,1}; }

        return b;
      }
    }.

    module RealEvaluator4 (MV : MVerifier_t) = {

      proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : (verifier_state_t * InTheHead5P.trace_t) option = {
        var r, c, ch, resp;
        var r_ss, r_mpc, rcs;
        var ws, x_mpc, tr, y;
        var cvs, vs, acceptance, bad;

        (r_ss, r_mpc, rcs) <- rp;

        ws <- SS5.share r_ss w;

        x_mpc <- mk_inputs x ws; (*map (fun pid => (pid, (x,oget (assoc ws pid)))) pid_set;*)
        (tr,y) <- MPC.protocol relc r_mpc x_mpc;

        vs <- map (fun pid => (pid, if pid = RP.k \/ pid = RP.l \/ pid = RP.m then (witness, witness, witness)
                                    else ((input pid x_mpc, rand pid r_mpc, trace pid tr)))) pid_set;
        cvs <- map (fun pid => 
                    let r_c = oget (assoc rcs pid) in
                    let ysv = oget (assoc vs pid) in 
                    (pid, (ysv, commit r_c ysv))) pid_set;
        c <- map (fun pid => (pid, fst (snd (oget (assoc cvs pid))))) pid_set;

        ch <@ MV.challenge(x, c);
        r <- None;
        bad <- ch <> (RP.i, RP.j);
        if (!bad) {
          resp <- InTheHead5P.response cvs ch;
          acceptance <- InTheHead5P.check (x,c,ch) resp;
          r <- Some ((x, c, ch), ((c, ch, resp)));
        }

        return r;
      }
    }.

    module E (D : Distinguisher_t) (RSS : SecretSharingSchemeSecurity.Rand_t, RMPC : Privacy.Rand_t,
              RCS1 : PCSRand_t, RCS2 : PCSRand_t, RCS3 : PCSRand_t,
               RCS4 : PCSRand_t, RCS5 : PCSRand_t, MV : MVerifier_t) = {

      module AllCSRand = AllCSRand(RCS1,RCS2,RCS3,RCS4,RCS5)

      var w : witness_t
      var x : statement_t
      var i, j, k, l, m : pid_mpc_t
      var vs : views_t
      var rcsi, rcsj, rcsk, rcsl : CS.rand_t

      proc choose(aux : Hiding.aux_t) : msg_t * msg_t * Hiding.aux_t = {
        var ws, x_mpc, tr, y;
        var r, rss, rmpc, dummy, wx, good;
    
        (wx,dummy,good) <- aux;
        (w,x) <- wx;

        rss <@ RSS.gen(x);
        r <- (witness,witness,(witness,witness,false));

        if (SS5.valid_rand rss w) {

          ws <- SS5.share rss w;
          (i,j) <$ InTheHead5P.challenge_distr;
          (k,l,m) <- get_other_pids i j;

          rmpc <@ RMPC.gen(relc, [i;j], x);

          rcsi <@ AllCSRand.gen(wx,i,true);
          rcsj <@ AllCSRand.gen(wx,j,true);
          rcsk <@ AllCSRand.gen(wx,k,true);
          rcsl <@ AllCSRand.gen(wx,l,true);

          if (valid_rands relc rmpc /\ valid_rand rcsi /\ valid_rand rcsj /\ valid_rand rcsk /\ valid_rand rcsl) {

            x_mpc <- mk_inputs x ws; (*map (fun pid => (pid, (x,oget (assoc ws pid)))) pid_set;*)
            (tr,y) <- MPC.protocol relc rmpc x_mpc;

            vs <- map (fun pid => (pid, if pid = k \/ pid = l \/ pid = m then (witness, witness, witness)
                                        else ((input pid x_mpc, rand pid rmpc, trace pid tr)))) pid_set;

            r <- ((witness, witness, witness), 
                  ((input m x_mpc, rand m rmpc, trace m tr)), (aux.`1, m,true));
            }
          }

        return r;
      }

      proc guess(fc : CS.commitment_t) : bool = {
        var resp;
        var ch, ci, cj, r;
        var ck, cl, c, cvs, acceptance, b, bad;

        ci <- CS.commit rcsi (oget (assoc vs i));
        cj <- CS.commit rcsj (oget (assoc vs j));
        ck <- CS.commit rcsk (oget (assoc vs k));
        cl <- CS.commit rcsl (oget (assoc vs l));

        cvs <- tuple5_to_list (assemble (i, (oget (assoc vs i), ci)) 
                                        (j, (oget (assoc vs j), cj))
                                        (k, (oget (assoc vs k), ck))
                                        (l, (oget (assoc vs l), cl))
                                        (m, (oget (assoc vs m), (fc,witness))));

        c <- tuple5_to_list (assemble (i, fst ci) (j, fst cj) (k, fst ck) (l, fst cl) (m, fc));
        ch <@ MV.challenge(x, c);

        bad <- ch <> (E.i, E.j);
        if (!bad) {
          resp <- InTheHead5P.response cvs ch;
          acceptance <- InTheHead5P.check (x,c,ch) resp;
          r <- ((x, c, ch), ((c, ch, resp)));
          b <@ D.guess(w, x, Some r);
          } else { b <@ D.guess(w, x, None); }

        return b;
      }
    }.

    module RealEvaluator5 (MV : MVerifier_t, S_MPC : Privacy.Simulator_t) = {

      proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : (verifier_state_t * InTheHead5P.trace_t) option = {
        var r, c, ch, resp;
        var r_ss, r_mpc, rcs;
        var ws, x_mpc;
        var cvs, vs, vsc, acceptance, bad, vi, vj, ys;
        var vk, vl, vm : view_t;

        (r_ss, r_mpc, rcs) <- rp;

        ws <- SS5.share r_ss w;

        x_mpc <- mk_inputs x ws; (*map (fun pid => (pid, (x,oget (assoc ws pid)))) pid_set;*)
        ys <- ProtocolFunctionality.f relc x_mpc;
        vsc <- S_MPC.simm(relc, [(RP.i, input RP.i x_mpc);(RP.j, input RP.j x_mpc)], r_mpc, 
                                [RP.i;RP.j],
                                [(RP.i, output RP.i ys);(RP.j, output RP.j ys)]);   
        vi <- (oget (assoc vsc RP.i));
        vj <- (oget (assoc vsc RP.j));
        vk <- witness;
        vl <- witness;
        vm <- witness;
        vs <- tuple5_to_list (assemble (RP.i, vi) (RP.j, vj) (RP.k, (witness, witness, witness)) (RP.l, (witness, witness, witness)) (RP.m, (witness, witness, witness)));

        cvs <- map (fun pid => 
                    let r_c = oget (assoc rcs pid) in
                    let v = oget (assoc vs pid) in 
                    (pid, (v, CS.commit r_c v))) pid_set;
        c <- map (fun pid => (pid, fst (snd (oget (assoc cvs pid))))) pid_set;

        ch <@ MV.challenge(x, c);
        r <- None;
        bad <- ch <> (RP.i, RP.j);
        if (!bad) {
          resp <- InTheHead5P.response cvs ch;
          acceptance <- InTheHead5P.check (x,c,ch) resp;
          r <- Some ((x, c, ch), ((c, ch, resp)));
        }

        return r;
      }
    }.

    module F (D : Distinguisher_t) (RSS : SecretSharingSchemeSecurity.Rand_t,
              RCS1 : PCSRand_t, RCS2 : PCSRand_t, RCS3 : PCSRand_t,
               RCS4 : PCSRand_t, RCS5 : PCSRand_t, MV : MVerifier_t) = {

      module AllCSRand = AllCSRand(RCS1,RCS2,RCS3,RCS4,RCS5)

      var inst : instance_t
      var i, j, k, l, m : pid_t
      var circ : circuit_t
      var xs : inputs_t
      var cr : pid_t list

      proc choose(circ_ : circuit_t, w : env_input_t, aux : Privacy.aux_t) : inputs_t * pid_t list = {
        var rss, ws;

        xs <- [];
        cr <- [];
        inst <- aux;
        circ <- circ_;
        (i,j) <$ InTheHead5P.challenge_distr;
        (k,l,m) <- get_other_pids i j;
        rss <@ RSS.gen(inst);
        if (valid_rand rss w) {
          ws <- share rss w;
          xs <- mk_inputs inst ws; (*map (fun pid => (pid, (inst, oget (assoc ws pid)))) pid_set;*)
          cr <- [i;j];
        }

        return (xs,cr);
        
      }

      proc guess(vsc : views_t) : bool = {
        var rcsi, rcsj, rcsk, rcsl, rcsm, rcs;
        var c, ch, xp;
        var bad, resp, vi, vj, r, b, cvs, vs, acceptance, w;

        vi <- oget (assoc vsc i);
        vj <- oget (assoc vsc j);

        xp <- pinput P1 xs;
        w <- reconstruct (map (fun pid => (pid, sinput pid xs)) pid_mpc_set);

        rcsi <@ AllCSRand.gen(witness,i,true);
        rcsj <@ AllCSRand.gen(witness,j,true);
        rcsk <@ AllCSRand.gen(witness,k,true);
        rcsl <@ AllCSRand.gen(witness,l,true);
        rcsm <@ AllCSRand.gen(witness,m,true);
        rcs <- tuple5_to_list (assemble (i,rcsi) (j,rcsj) (k,rcsk) (l,rcsl) (m,rcsm));

        if (valid_rand rcsi /\ valid_rand rcsj /\ valid_rand rcsk /\
            valid_rand rcsl /\ valid_rand rcsm) {

          vs <- tuple5_to_list (assemble (i, vi) (j, vj) (k, (witness, witness, witness)) (l, (witness, witness, witness)) (m, (witness, witness, witness)));


          cvs <- map (fun pid => 
                      let r_c = oget (assoc rcs pid) in
                      let v = oget (assoc vs pid) in 
                      (pid, (v, CS.commit r_c v))) pid_set;
          c <- map (fun pid => (pid, fst (snd (oget (assoc cvs pid))))) pid_set;

          ch <@ MV.challenge(inst, c);

          bad <- ch <> (i, j);
          if (!bad) {
            resp <- InTheHead5P.response cvs ch;
            acceptance <- InTheHead5P.check (inst, c, ch) resp;
            r <- ((inst, c, ch), ((c, ch, resp)));
            b <@ D.guess(w, inst, Some r);
          } else { b <@ D.guess(w, inst, None); }
        } else { b <$ {0,1}; }

        return b;
      }
    }.

    module Simulator (RSS : SecretSharingSchemeSecurity.Rand_t, RMPC : Privacy.Rand_t, RCS1 : PCSRand_t, RCS2 : PCSRand_t, RCS3 : PCSRand_t,
               RCS4 : PCSRand_t, RCS5 : PCSRand_t, MV : MVerifier_t, S_MPC : Privacy.Simulator_t,
                      S_SS : SecretSharingSchemeSecurity.Simulator_t) = {

      module AllCSRand = AllCSRand(RCS1,RCS2,RCS3,RCS4,RCS5)

      var cvs : committed_views_t
      var c : InTheHead5P.commitment_t

      proc gen_commitment(rp : prover_rand_t, x : statement_t) : InTheHead5P.commitment_t option = {
        var rcs, rss, rmpc, r_cs;
        var vs, vsc, vi, vj, xsc;
        var vk, vl, vm : view_t;

        (rss, rmpc, r_cs) <- rp;

        xsc <- S_SS.simm(x, rss, [RP.i; RP.j]);

        vsc <- S_MPC.simm(relc, 
                          [(RP.i, (x, get_party_share RP.i xsc)); 
                            (RP.j, (x, get_party_share RP.j xsc))],
                          rmpc,
                          [RP.i;RP.j], [(RP.i, true);(RP.j, true)]);  
        vi <- oget (assoc vsc RP.i);
        vj <- oget (assoc vsc RP.j);
        vk <- (witness, witness, witness);
        vl <- (witness, witness, witness);
        vm <- (witness, witness, witness);
        vs <- tuple5_to_list (assemble (RP.i, vi) (RP.j, vj) (RP.k, vk) (RP.l, vl) (RP.m, vm));

        rcs <- tuple5_to_list (assemble (RP.i,RP.rcsi) (RP.j,RP.rcsj) (RP.k,RP.rcsk) (RP.l,RP.rcsl) (RP.m,RP.rcsm));

        cvs <- map (fun pid => 
                    let r_c = oget (assoc rcs pid) in
                    let v = oget (assoc vs pid) in 
                    (pid, (v, CS.commit r_c v))) pid_set;
        c <- map (fun pid => (pid, fst (snd (oget (assoc cvs pid))))) pid_set;


        return (Some c);
      }

      proc gen_response(x : statement_t, ch : challenge_t) : response_t option = {
        var r, bad, resp;

        r <- None;
        bad <- ch <> (RP.i, RP.j);
        if (!bad) {
          resp <- InTheHead5P.response cvs ch;
          r <- Some resp;
        }

        return r;
      }
    }.

    module G (D : Distinguisher_t) (RMPC : Privacy.Rand_t, RCS1 : PCSRand_t, RCS2 : PCSRand_t, RCS3 : PCSRand_t,
               RCS4 : PCSRand_t, RCS5 : PCSRand_t, MV : MVerifier_t, S_MPC : Privacy.Simulator_t) = {

      module AllCSRand = AllCSRand(RCS1,RCS2,RCS3,RCS4,RCS5)

      var inst : instance_t
      var i, j, k, l, m : pid_t
      var cr : pid_t list

      proc choose(aux : aux_t) : pid_t list = {
        inst <- aux;
        (i,j) <$ InTheHead5P.challenge_distr;
        (k,l,m) <- get_other_pids i j;
        cr <- [i;j];
        return cr;
      }

      proc guess(s : secret_t, ss : shares_t) : bool = {
        var rcsi, rcsj, rcsk, rcsl, rcsm, rcs;
        var c, ch, s_safe;
        var bad, resp, vi, vj, r, b, cvs, vs, acceptance;
        var vsc, rmpc;

        s_safe <- s;

        rmpc <@ RMPC.gen(relc, [i;j], inst);

        vsc <- S_MPC.simm(relc, [(G.i, (inst, get_party_share G.i ss)); (G.j, (inst, get_party_share G.j ss))], rmpc, [G.i;G.j], [(G.i, relation s inst);(G.j, relation s inst)]);  
        vi <- oget (assoc vsc i);
        vj <- oget (assoc vsc j);
        vs <- tuple5_to_list (assemble (i, vi) (j, vj) (k, (witness, witness, witness)) (l, (witness, witness, witness)) (m, (witness, witness, witness)));

        rcsi <@ AllCSRand.gen(witness,i,relation s_safe inst);
        rcsj <@ AllCSRand.gen(witness,j,relation s_safe inst);
        rcsk <@ AllCSRand.gen(witness,k,relation s_safe inst);
        rcsl <@ AllCSRand.gen(witness,l,relation s_safe inst);
        rcsm <@ AllCSRand.gen(witness,m,relation s_safe inst);
        rcs <- tuple5_to_list (assemble (i,rcsi) (j,rcsj) (k,rcsk) (l,rcsl) (m,rcsm));

        if (valid_rand rcsi /\ valid_rand rcsj /\ valid_rand rcsk /\
            valid_rand rcsl /\ valid_rand rcsm /\ valid_rands relc rmpc) {

          cvs <- map (fun pid => 
                      let r_c = oget (assoc rcs pid) in
                      let v = oget (assoc vs pid) in 
                      (pid, (v, CS.commit r_c v))) pid_set;
          c <- map (fun pid => (pid, fst (snd (oget (assoc cvs pid))))) pid_set;

          ch <@ MV.challenge(inst, c);

          bad <- ch <> (i, j);
          if (!bad) {
            resp <- InTheHead5P.response cvs ch;
            acceptance <- InTheHead5P.check (inst, c, ch) resp;
            r <- ((inst, c, ch), ((c, ch, resp)));
            b <@ D.guess(s, inst, Some r);
          } else { b <@ D.guess(s, inst, None); }
        } else { b <$ {0,1}; }

        return b;
      }
    }.

    declare module RSS : SecretSharingSchemeSecurity.Rand_t{RP,B,C,E,Hiding.Game,F,G,Simulator}.
    declare module RMPC : Privacy.Rand_t{RP,RSS,B,C,E,Hiding.Game,F,G,Simulator}.
    declare module RCS1 : PCSRand_t{RP,RSS,RMPC,B,C,E,Hiding.Game,F,G,Simulator}.
    declare module RCS2 : PCSRand_t{RP,RSS,RMPC,RCS1,B,C,E,Hiding.Game,F,G,Simulator}.
    declare module RCS3 : PCSRand_t{RP,RSS,RMPC,RCS1,RCS2,B,C,E,Hiding.Game,F,G,Simulator}.
    declare module RCS4 : PCSRand_t{RP,RSS,RMPC,RCS1,RCS2,RCS3,B,C,E,Hiding.Game,F,G,Simulator}.
    declare module RCS5 : PCSRand_t{RP,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,B,C,E,Hiding.Game,F,G,Simulator}.

    axiom rss_ll : islossless RSS.gen.
    axiom rmpc_ll : islossless RMPC.gen.
    axiom rcs1_ll : islossless RCS1.gen.
    axiom rcs2_ll : islossless RCS2.gen.
    axiom rcs3_ll : islossless RCS3.gen.
    axiom rcs4_ll : islossless RCS4.gen.
    axiom rcs5_ll : islossless RCS5.gen.
    lemma ccsrandp_ll : islossless AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5).gen.
    proof. 
      apply (csrandp_ll RCS1 RCS2 RCS3 RCS4 RCS5); [apply rcs1_ll | apply rcs2_ll | apply rcs3_ll | apply rcs4_ll | apply rcs5_ll ].
    qed.

    declare module D : Distinguisher_t{RP,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,B,C,E,Hiding.Game,F,G,Simulator}.
    declare module MV : MVerifier_t{RP,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,D,B,C,E,Hiding.Game,F,G,Simulator}.
    declare module S_MPC : Privacy.Simulator_t{RP,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,D,B,C,E,Hiding.Game,F,G,MV,Simulator}.
    axiom s_mpc_ll : islossless S_MPC.simm.
    declare module S_SS : SecretSharingSchemeSecurity.Simulator_t{RP,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,D,B,C,E,Hiding.Game,F,G,MV,S_MPC,Simulator}.
    axiom s_ss_ll : islossless S_SS.simm.

    local module GameReal0 = ZKGame(D,RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5),RealEvaluator0(MV)).
    local module GameReal1 = ZKGame(D,RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5),RealEvaluator1(MV)).
    local module GameReal2 = ZKGame(D,RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5),RealEvaluator2(MV)).
    local module GameReal3 = ZKGame(D,RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5),RealEvaluator3(MV)).
    local module GameReal4 = ZKGame(D,RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5),RealEvaluator4(MV)).
    local module GameReal5 = ZKGame(D,RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5),RealEvaluator5(MV,S_MPC)).

    lemma pairwise_eq (x y : 'a * 'b) : x = y <=> x.`1 = y.`1 /\ x.`2 = y.`2 by [].

    local lemma real_real0_equiv : 
      equiv [ GameReal(D, RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5), MV).main ~ 
              GameReal0.main : 
              ={glob MV, glob D, glob RSS, glob RMPC,
                glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5, w, x} ==> ={res} ].
    proof.
      proc.
      seq 1 1 : (#pre /\ ={rp}).
        inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
        sp; seq 1 1 : (#pre /\ ={RP.i,RP.j} /\ (RP.i, RP.j){1} \in InTheHead5P.challenge_distr); first by rnd; skip => /#.
        sp; seq 1 1 : (#pre /\ ={rss}); first by call (_ : true).
        sp; seq 1 1 : (#pre /\ ={rmpc}); first by call (_ : true). 
        by wp; do call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      (if; last by rnd); first by done.
      inline*.
      call (_ : true); wp; call (_ : true); wp; skip; progress.
        rewrite /commit /=. 
        elim (rp{2}) => rss rmpc rcs /=.
        have : exists tr y, (tr,y) = protocol relc rmpc (mk_inputs x{2} (share rss w{2})).
          by exists (protocol relc rmpc (mk_inputs x{2} (share rss w{2}))).`1 (protocol relc rmpc (mk_inputs x{2} (share rss w{2}))).`2 => /#.
        move => H0; elim H0 => tr y H0 /=; rewrite -H0 /=.
        rewrite -eq_in_map /= => pid H1; rewrite !map_assoc //=.
rewrite !map_assoc //=.
rewrite /input /trace /mk_inputs.
rewrite !map_assoc //=.
smt().
        rewrite /commit /response /=. 
        elim (rp{2}) => rss rmpc rcs /=.
        have : exists tr y, (tr,y) = protocol relc rmpc (mk_inputs x{2} (share rss w{2})).
          by exists (protocol relc rmpc (mk_inputs x{2} (share rss w{2}))).`1 (protocol relc rmpc (mk_inputs x{2} (share rss w{2}))).`2 => /#.
        move => H1; elim H1 => tr y H1 /=; rewrite -H1 /=.
        elim result_R => i j /=.
        rewrite /get_party_committed_view /=.
        case (i \in pid_set) => H2; last by smt().
        case (j \in pid_set) => H3; last by smt().
        by rewrite !map_assoc //= !map_assoc //= => /#.
    qed.

    local lemma real_real0_pr &m x : 
      Pr[GameReal(D, RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5), MV).main(x) @ &m : res] = 
      Pr[GameReal0.main(x) @ &m : res].
    proof. by byequiv real_real0_equiv. qed.

    local lemma real1_commitment1 : 
      equiv [ GameReal1.main ~ 
              Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       B(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game :
              ={glob D, glob RSS, glob RMPC, glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5,  
                glob MV} /\ (w{1},x{1}) = aux{2}.`1 /\ b{2} ==> ={res} ].
    proof.
      proc; inline B(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).choose.
      inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
      sp; swap{1} 3-2; seq 1 1 : (#pre /\ ={rss}); first by call (_:true).
      sp; if{2}; last first.
        rcondf{1} 11; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          seq 1 : (#pre); first by rnd. 
          sp; seq 1  : (true); first by call (_: true).
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; call{1} rmpc_ll; wp; rnd{1}; skip; 
              rewrite challenge_distr_ll.
      sp; seq 1 1 : (#pre /\ RP.i{1} = B.i{2} /\ RP.j{1} = B.j{2} /\ (B.i{2},B.j{2}) \in InTheHead5P.challenge_distr); first by rnd; skip => /#.
      sp; seq 1 1 : (#pre /\ ={rmpc}); first by call (_: true).
      sp; seq 1 1 : (#pre /\ RP.rcsi{1} = B.rcsi{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      sp; seq 1 1 : (#pre /\ RP.rcsj{1} = B.rcsj{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      if{2}; last first.
        rcondf{1} 5; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first by move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; skip.
      sp; seq 1 1 : (#pre /\ RP.rcsk{1} = r{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; if{2}; last first.
        rcondf{1} 4; first move => &m; wp. 
          conseq (_ : true ==> true); first by smt().
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        by rnd; wp; do call{1} ccsrandp_ll; skip => /#.
      inline B(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).guess.
      sp; seq 1 1 : (#pre /\ RP.rcsl{1} = rcsl{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; seq 1 1 : (#pre /\ RP.rcsm{1} = rcsm{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; if; last by wp; rnd; skip => /#.
        rewrite /valid_rand_prover => /> &1 &2 ???? H1 H2 ??? H5;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H1 H2 H5;
          case (B.i{2}); case (B.j{2}) => //; smt(challenge_distr_diff).
      inline RealEvaluator1(MV).eval; sp.
      seq 1 1 : (#pre /\ ={ch}); first call (_ : true); skip; progress. 
        move : H2 H3 H6 H0 H12.
        rewrite H4 /= /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: B.i{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.j{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.l{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.m{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 4 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H13; move : H2 H3 H6.
        by case (B.i{2}); case (B.j{2}) => /= /> *; 
          rewrite !map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
      sp 2 1; if => //; last by wp; call (_ : true); wp; skip; progress => /#.
      wp; call (_ : true); wp; skip; progress.
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: B.i{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.j{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.l{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.m{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 4 by smt().
        move : H2 H3; rewrite /pid_set /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H13; move : H2 H3 H6.
         by case (B.i{2}); case (B.j{2}) => /= /> *;
          rewrite !map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: B.i{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.j{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.l{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.m{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 4 by smt().
        move : H2 H3; rewrite /pid_set /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H13; move : H2 H3 H6.
        by case (B.i{2}); case (B.j{2}) => /= /> *;
          rewrite !map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 6 by smt(). 
        move => H2 H3.
        have ->: B.i{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.j{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.l{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.m{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 4 by smt().
        move : H2 H3; rewrite /pid_set /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H13; move : H2 H3 H6.
        by case (B.i{2}); case (B.j{2}) => /= /> *;
          rewrite !map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
    qed.

    local lemma real2_commitment0 : 
      equiv [ GameReal2.main ~ 
              Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       B(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game :
              ={glob D, glob RSS, glob RMPC, glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5,  
                glob MV} /\ (w{1},x{1}) = aux{2}.`1 /\ !b{2} ==> res{1} <> res{2} ].
    proof.
      proc; inline B(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).choose.
      inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
      sp; swap{1} 3-2; seq 1 1 : (#pre /\ ={rss}); first by call (_:true).
      sp; if{2}; last first.
        rcondf{1} 11; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          seq 1 : (#pre); first by rnd. 
          sp; seq 1  : (true); first by call (_: true).
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; call{1} rmpc_ll; wp; rnd{1}; skip; 
              rewrite challenge_distr_ll.
      sp; seq 1 1 : (#pre /\ RP.i{1} = B.i{2} /\ RP.j{1} = B.j{2} /\ (B.i{2},B.j{2}) \in InTheHead5P.challenge_distr); first by rnd; skip => /#.
      sp; seq 1 1 : (#pre /\ ={rmpc}); first by call (_: true).
      sp; seq 1 1 : (#pre /\ RP.rcsi{1} = B.rcsi{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      sp; seq 1 1 : (#pre /\ RP.rcsj{1} = B.rcsj{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      if{2}; last first.
        rcondf{1} 5; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first by move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; skip.
      sp; seq 1 1 : (#pre /\ RP.rcsk{1} = r{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; if{2}; last first.
        rcondf{1} 4; first move => &m; wp. 
          conseq (_ : true ==> true); first by smt().
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        by rnd; wp; do call{1} ccsrandp_ll; skip => /#.
      inline B(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).guess.
      sp; seq 1 1 : (#pre /\ RP.rcsl{1} = rcsl{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; seq 1 1 : (#pre /\ RP.rcsm{1} = rcsm{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; if; last by wp; rnd; skip => /#.
       by rewrite /valid_rand_prover => /> &1 &2 ???? H1 H2 ??? H5;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H1 H2 H5;
          case (B.i{2}); case (B.j{2}) => //; smt(challenge_distr_diff).
      inline RealEvaluator2(MV).eval; sp.
      seq 1 1 : (#pre /\ ={ch}); first call (_ : true); skip; progress. 
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 4 by smt().
        move => H2 H3.
        have ->: B.i{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.j{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.l{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.m{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 4 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H13. move : H2 H3 H6.
        by case (B.i{2}); case (B.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
      sp 2 1; if => //; last by wp; call (_ : true); wp; skip; progress => /#.
      wp; call (_ : true); wp; skip; progress.
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 4 by smt().
        move => H2 H3.
        have ->: B.i{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.j{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.l{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.m{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 4 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H13; move : H2 H3 H6.
          by case (B.i{2}); case (B.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 4 by smt().
        move => H2 H3.
        have ->: B.i{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.j{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.l{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.m{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 4 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H13; move : H2 H3 H6.
        by case (B.i{2}); case (B.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt(). 
        move => H2 H3.
        have ->: B.i{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.j{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.l{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        have ->: B.m{2} = B.k{2} <=> false by move : H2 H3; case (B.i{2}); case (B.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 4 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H13; move : H2 H3 H6.
        by case (B.i{2}); case (B.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
    qed.

    local lemma adv_commitment_hop1 &m x : 
      Pr[GameReal1.main(x) @ &m : res] - Pr[GameReal2.main(x) @ &m : res] <= 
      Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       B(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x, witness,true),true) @ &m : res] - 
      Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       B(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),false) @ &m : !res].
    proof.
      have ->: Pr[GameReal1.main(x) @ &m : res] = 
              Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       B(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),true) @ &m : res] 
        by byequiv real1_commitment1 => /#.
      have ->: Pr[GameReal2.main(x) @ &m : res] = 
              Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       B(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),false) @ &m : !res] 
        by byequiv real2_commitment0 => /= /#.
      by done.
    qed.

    local lemma real2_commitment1 : 
      equiv [ GameReal2.main ~ 
              Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       C(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game :
              ={glob D, glob RSS, glob RMPC, glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5,
                glob MV} /\ (w{1},x{1}) = aux{2}.`1 /\ b{2} ==> ={res} ].
    proof.
      proc; inline C(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).choose.
      inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
      sp; swap{1} 3-2; seq 1 1 : (#pre /\ ={rss}); first by call (_:true).
      sp; if{2}; last first.
        rcondf{1} 11; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          seq 1 : (#pre); first by rnd. 
          sp; seq 1  : (true); first by call (_: true).
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; call{1} rmpc_ll; wp; rnd{1}; skip; 
              rewrite challenge_distr_ll.
      sp; seq 1 1 : (#pre /\ RP.i{1} = C.i{2} /\ RP.j{1} = C.j{2} /\ (C.i{2},C.j{2}) \in InTheHead5P.challenge_distr); first by rnd; skip => /#.
      sp; seq 1 1 : (#pre /\ ={rmpc}); first by call (_: true).
      sp; seq 1 1 : (#pre /\ RP.rcsi{1} = C.rcsi{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      sp; seq 1 1 : (#pre /\ RP.rcsj{1} = C.rcsj{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      sp; seq 1 1 : (#pre /\ RP.rcsk{1} = C.rcsk{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      if{2}; last first.
        rcondf{1} 4; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first by move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; skip.
      sp; seq 1 1 : (#pre /\ RP.rcsl{1} = r{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; if{2}; last first.
        rcondf{1} 3; first move => &m; wp. 
          conseq (_ : true ==> true); first by smt(). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        by rnd; wp; do call{1} ccsrandp_ll; skip => /#.
      inline C(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).guess.
      sp; seq 1 1 : (#pre /\ RP.rcsm{1} = rcsm{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; if; last by wp; rnd; skip => /#.
        by rewrite /valid_rand_prover; progress;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H1 H2 H5;
          case (C.i{2}); case (C.j{2}) => //; smt(challenge_distr_diff).
      inline RealEvaluator2(MV).eval; sp.
      seq 1 1 : (#pre /\ ={ch}); first call (_ : true); skip; progress. 
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: C.i{2} = C.k{2} \/ C.i{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.j{2} = C.k{2} \/ C.j{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.m{2} = C.k{2} \/ C.m{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 3 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (C.i{2}); case (C.j{2}) => /= /> *; 
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
      sp 2 1; if => //; last by wp; call (_ : true); wp; skip; progress => /#.
      wp; call (_ : true); wp; skip; progress.
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: C.i{2} = C.k{2} \/ C.i{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.j{2} = C.k{2} \/ C.j{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.m{2} = C.k{2} \/ C.m{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 3 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (C.i{2}); case (C.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: C.i{2} = C.k{2} \/ C.i{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.j{2} = C.k{2} \/ C.j{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.m{2} = C.k{2} \/ C.m{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 3 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (C.i{2}); case (C.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 6 by smt().
        move => H2 H3.
        have ->: C.i{2} = C.k{2} \/ C.i{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.j{2} = C.k{2} \/ C.j{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.m{2} = C.k{2} \/ C.m{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 3 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (C.i{2}); case (C.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
    qed.

    local lemma real3_commitment0 : 
      equiv [ GameReal3.main ~ 
              Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       C(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game :
              ={glob D, glob RSS, glob RMPC, glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5,
                glob MV} /\ (w{1},x{1}) = aux{2}.`1 /\ !b{2} ==> res{1} <> res{2} ].
    proof.
      proc; inline C(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).choose.
      inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
      sp; swap{1} 3-2; seq 1 1 : (#pre /\ ={rss}); first by call (_:true).
      sp; if{2}; last first.
        rcondf{1} 11; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          seq 1 : (#pre); first by rnd. 
          sp; seq 1  : (true); first by call (_: true).
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; call{1} rmpc_ll; wp; rnd{1}; skip; 
              rewrite challenge_distr_ll.
      sp; seq 1 1 : (#pre /\ RP.i{1} = C.i{2} /\ RP.j{1} = C.j{2} /\ (C.i{2},C.j{2}) \in InTheHead5P.challenge_distr); first by rnd; skip => /#.
      sp; seq 1 1 : (#pre /\ ={rmpc}); first by call (_: true).
      sp; seq 1 1 : (#pre /\ RP.rcsi{1} = C.rcsi{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      sp; seq 1 1 : (#pre /\ RP.rcsj{1} = C.rcsj{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      sp; seq 1 1 : (#pre /\ RP.rcsk{1} = C.rcsk{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      if{2}; last first.
        rcondf{1} 4; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first by move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; skip.
      sp; seq 1 1 : (#pre /\ RP.rcsl{1} = r{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; if{2}; last first.
        rcondf{1} 3; first move => &m; wp. 
          conseq (_ : true ==> true); first by smt().
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        by rnd; wp; do call{1} ccsrandp_ll; skip => /#.
      inline C(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).guess.
      sp; seq 1 1 : (#pre /\ RP.rcsm{1} = rcsm{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; if; last by wp; rnd; skip => /#.
       by rewrite /valid_rand_prover => /> &1&2 ???? H1 H2 ??? H5;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H1 H2 H5;
          case (C.i{2}); case (C.j{2}) => //; smt(challenge_distr_diff).
      inline RealEvaluator3(MV).eval; sp.
      seq 1 1 : (#pre /\ ={ch}); first call (_ : true); skip; progress. 
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 4 by smt().
        move => H2 H3.
        have ->: C.i{2} = C.k{2} \/ C.i{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.j{2} = C.k{2} \/ C.j{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.m{2} = C.k{2} \/ C.m{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 3 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (C.i{2}); case (C.j{2}) => /= /> *; 
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
      sp 2 1; if => //; last by wp; call (_ : true); wp; skip; progress => /#.
      wp; call (_ : true); wp; skip; progress.
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 4 by smt().
        move => H2 H3.
        have ->: C.i{2} = C.k{2} \/ C.i{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.j{2} = C.k{2} \/ C.j{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.m{2} = C.k{2} \/ C.m{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 3 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (C.i{2}); case (C.j{2}) => /= /> *; 
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 4 by smt().
        move => H2 H3.
        have ->: C.i{2} = C.k{2} \/ C.i{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.j{2} = C.k{2} \/ C.j{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.m{2} = C.k{2} \/ C.m{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 3 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (C.i{2}); case (C.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H0.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: C.i{2} = C.k{2} \/ C.i{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.j{2} = C.k{2} \/ C.j{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        have ->: C.m{2} = C.k{2} \/ C.m{2} = C.l{2} <=> false by move : H2 H3; case (C.i{2}); case (C.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 3 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (C.i{2}); case (C.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
    qed.

    local lemma adv_commitment_hop2 &m x : 
      Pr[GameReal2.main(x) @ &m : res] - Pr[GameReal3.main(x) @ &m : res] <= 
      Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       C(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),true) @ &m : res] - 
      Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       C(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),false) @ &m : !res].
    proof.
      have ->: Pr[GameReal2.main(x) @ &m : res] = 
              Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       C(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),true) @ &m : res] 
        by byequiv real2_commitment1 => /#.
      have ->: Pr[GameReal3.main(x) @ &m : res] = 
              Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       C(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),false) @ &m : !res] 
        by byequiv real3_commitment0 => /= /#.
      by done.
    qed.

    local lemma real3_commitment1 : 
      equiv [ GameReal3.main ~ 
              Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       E(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game :
              ={glob D, glob RSS, glob RMPC, glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5,
                glob MV} /\ (w{1},x{1}) = aux{2}.`1 /\ b{2} ==> ={res} ].
    proof.
      proc; inline E(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).choose.
      inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
      sp; swap{1} 3-2; seq 1 1 : (#pre /\ ={rss}); first by call (_:true).
      sp; if{2}; last first.
        rcondf{1} 11; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          seq 1 : (#pre); first by rnd. 
          sp; seq 1  : (true); first by call (_: true).
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; call{1} rmpc_ll; wp; rnd{1}; skip; 
              rewrite challenge_distr_ll.
      sp; seq 1 1 : (#pre /\ RP.i{1} = E.i{2} /\ RP.j{1} = E.j{2} /\ (E.i{2},E.j{2}) \in InTheHead5P.challenge_distr); first by rnd; skip => /#.
      sp; seq 1 1 : (#pre /\ ={rmpc}); first by call (_: true).
      sp; seq 1 1 : (#pre /\ RP.rcsi{1} = E.rcsi{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      sp; seq 1 1 : (#pre /\ RP.rcsj{1} = E.rcsj{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      sp; seq 1 1 : (#pre /\ RP.rcsk{1} = E.rcsk{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; seq 1 1 : (#pre /\ RP.rcsl{1} = E.rcsl{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.      
      if{2}; last first.
        rcondf{1} 3; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first by move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; skip.
      sp; seq 1 1 : (#pre /\ RP.rcsm{1} = r{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#. 
      sp; if{2}; last first.
        rcondf{1} 1; first move => &m; wp. 
          conseq (_ : true ==> true); first by smt().
          by done.
        by rnd; skip => /#.
      inline E(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).guess.
      rcondt{1} 1.
        move => &m; skip; progress.
        by rewrite /valid_rand_prover; progress;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H0 H1 H4;
          case (E.i{m}); case (E.j{m}) => //; smt(challenge_distr_diff).
        by rewrite /valid_rand_prover =>*;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H0 H1 H4;
          case (E.i{m}); case (E.j{m}) => //; smt(challenge_distr_diff).
        by rewrite /valid_rand_prover => *;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H0 H1 H4;
          case (E.i{m}); case (E.j{m}) => //; smt(challenge_distr_diff).
        by rewrite /valid_rand_prover => *;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H0 H1 H4;
          case (E.i{m}); case (E.j{m}) => //; smt(challenge_distr_diff).
        by rewrite /valid_rand_prover => *;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H0 H1 H4;
          case (E.i{m}); case (E.j{m}) => //; smt(challenge_distr_diff).
      inline RealEvaluator3(MV).eval; sp.
      seq 1 1 : (#pre /\ ={ch}); first call (_ : true); skip; progress. 
        move : H2 H3 H6 H.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: E.i{2} = E.k{2} \/ E.i{2} = E.l{2} \/ E.i{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        have ->: E.j{2} = E.k{2} \/ E.j{2} = E.l{2} \/ E.j{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 2 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (E.i{2}); case (E.j{2}) => /= /> *; 
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
      sp 2 1; if => //; last by wp; call (_ : true); wp; skip; progress => /#.
      wp; call (_ : true); wp; skip; progress.
        move : H2 H3 H6 H.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: E.i{2} = E.k{2} \/ E.i{2} = E.l{2} \/ E.i{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        have ->: E.j{2} = E.k{2} \/ E.j{2} = E.l{2} \/ E.j{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 2 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (E.i{2}); case (E.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: E.i{2} = E.k{2} \/ E.i{2} = E.l{2} \/ E.i{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        have ->: E.j{2} = E.k{2} \/ E.j{2} = E.l{2} \/ E.j{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 2 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (E.i{2}); case (E.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 6 by smt().
        move => H2 H3.
        have ->: E.i{2} = E.k{2} \/ E.i{2} = E.l{2} \/ E.i{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        have ->: E.j{2} = E.k{2} \/ E.j{2} = E.l{2} \/ E.j{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 2 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (E.i{2}); case (E.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
    qed.

    local lemma real4_commitment0 : 
      equiv [ GameReal4.main ~ 
              Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       E(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game :
              ={glob D, glob RSS, glob RMPC, glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5,
                glob MV} /\ (w{1},x{1}) = aux{2}.`1 /\ !b{2} ==> res{1} <> res{2} ].
    proof.
      proc; inline E(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).choose.
      inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
      sp; swap{1} 3-2; seq 1 1 : (#pre /\ ={rss}); first by call (_:true).
      sp; if{2}; last first.
        rcondf{1} 11; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          seq 1 : (#pre); first by rnd. 
          sp; seq 1  : (true); first by call (_: true).
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; call{1} rmpc_ll; wp; rnd{1}; skip; 
              rewrite challenge_distr_ll.
      sp; seq 1 1 : (#pre /\ RP.i{1} = E.i{2} /\ RP.j{1} = E.j{2} /\ (E.i{2},E.j{2}) \in InTheHead5P.challenge_distr); first by rnd; skip => /#.
      sp; seq 1 1 : (#pre /\ ={rmpc}); first by call (_: true).
      sp; seq 1 1 : (#pre /\ RP.rcsi{1} = E.rcsi{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      sp; seq 1 1 : (#pre /\ RP.rcsj{1} = E.rcsj{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5).
      sp; seq 1 1 : (#pre /\ RP.rcsk{1} = E.rcsk{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.
      sp; seq 1 1 : (#pre /\ RP.rcsl{1} = E.rcsl{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#.      
      if{2}; last first.
        rcondf{1} 3; first move => &m; wp. 
          conseq (_ : true ==> true); first by rewrite /valid_rand_prover => /#.
          sp; seq 1  : (true); first by call (_: true). 
          by done.
        rcondf{2} 3; first by move => &m; wp; (call (_ : true); first by if => //); wp; skip => /#.
        rnd; wp.
        conseq (_ : true ==> true); first by smt().
        by do call{1} ccsrandp_ll; call{2} ccsrandp_ll; wp; skip.
      sp; seq 1 1 : (#pre /\ RP.rcsm{1} = r{2}); 
        first by call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip => /#. 
      sp; if{2}; last first.
        rcondf{1} 1; first move => &m; wp. 
          conseq (_ : true ==> true); first by smt().
          by done.
        by rnd; skip => /#.
      inline E(D, RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV).guess.
      rcondt{1} 1.
        move => &m; skip; progress.
        by rewrite /valid_rand_prover; progress;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H0 H1 H4;
          case (E.i{m}); case (E.j{m}) => //; smt(challenge_distr_diff).
        by rewrite /valid_rand_prover => *;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H0 H1 H4;
          case (E.i{m}); case (E.j{m}) => //; smt(challenge_distr_diff).
        by rewrite /valid_rand_prover => *;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H0 H1 H4;
          case (E.i{m}); case (E.j{m}) => //; smt(challenge_distr_diff).
        by rewrite /valid_rand_prover => *;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H0 H1 H4;
          case (E.i{m}); case (E.j{m}) => //; smt(challenge_distr_diff).
        by rewrite /valid_rand_prover => *;
          rewrite /tuple5_to_list /assemble /= /replace5_tuple;
          move : H0 H1 H4;
          case (E.i{m}); case (E.j{m}) => //; smt(challenge_distr_diff).
      inline RealEvaluator4(MV).eval; sp.
      seq 1 1 : (#pre /\ ={ch}); first call (_ : true); skip; progress. 
        move : H2 H3 H6 H.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 4 by smt().
        move => H2 H3.
        have ->: E.i{2} = E.k{2} \/ E.i{2} = E.l{2} \/ E.i{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        have ->: E.j{2} = E.k{2} \/ E.j{2} = E.l{2} \/ E.j{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 2 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (E.i{2}); case (E.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
      sp 2 1; if => //; last by wp; call (_ : true); wp; skip; progress => /#.
      wp; call (_ : true); wp; skip; progress.
        move : H2 H3 H6 H.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 4 by smt().
        move => H2 H3.
        have ->: E.i{2} = E.k{2} \/ E.i{2} = E.l{2} \/ E.i{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        have ->: E.j{2} = E.k{2} \/ E.j{2} = E.l{2} \/ E.j{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 2 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (E.i{2}); case (E.j{2}) => /= /> *; 
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 4 by smt().
        move => H2 H3.
        have ->: E.i{2} = E.k{2} \/ E.i{2} = E.l{2} \/ E.i{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        have ->: E.j{2} = E.k{2} \/ E.j{2} = E.l{2} \/ E.j{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 2 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (E.i{2}); case (E.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        move : H2 H3 H6 H.
        rewrite H4 /tuple5_to_list /assemble /= /replace5_tuple /input.
        rewrite !map_assoc //=; first 5 by smt().
        move => H2 H3.
        have ->: E.i{2} = E.k{2} \/ E.i{2} = E.l{2} \/ E.i{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        have ->: E.j{2} = E.k{2} \/ E.j{2} = E.l{2} \/ E.j{2} = E.m{2} <=> false by move : H2 H3; case (E.i{2}); case (E.j{2}) => /#.
        rewrite /input /commit /= !map_assoc //=; first 2 by smt().
        move : H2 H3; rewrite /pid_set /= /pid_mpc_set /= !assocP1 !assocP2 !assocP3 !assocP4 !assocP5 /=.
        move => H2 H3 H6 H14; move : H2 H3 H6.
        by case (E.i{2}); case (E.j{2}) => /= /> *;
          rewrite ?map_assoc //=; smt(challenge_distr_diff assocP1 assocP2 assocP3 assocP4 assocP5).
        by smt().
    qed.

    local lemma adv_commitment_hop3 &m x : 
      Pr[GameReal3.main(x) @ &m : res] - Pr[GameReal4.main(x) @ &m : res] <= 
      Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       E(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),true) @ &m : res] - 
      Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       E(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),false) @ &m : !res].
    proof.
      have ->: Pr[GameReal3.main(x) @ &m : res] = 
              Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       E(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),true) @ &m : res] 
        by byequiv real3_commitment1 => /#.
      have ->: Pr[GameReal4.main(x) @ &m : res] = 
              Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       E(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game((x,witness,true),false) @ &m : !res] 
        by byequiv real4_commitment0 => /= /#.
      by done.
    qed.

    local lemma real4_privacy_real : 
      equiv [ GameReal4.main ~ 
              Privacy.GameReal(F(D,RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV), RMPC).main :
              ={glob D, glob RSS, glob RMPC, glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5,
                glob MV} /\ c{2} = relc /\ x{1} = aux{2} /\ valid_secret w{1} /\ w{1} = x{2}
                ==> ={res} ].
    proof.
      proc.
      inline F(D, RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV).choose.
      inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
      sp; seq 1 1 : (#pre /\ RP.i{1} = F.i{2} /\ RP.j{1} = F.j{2} /\
                    (F.i, F.j){2} \in InTheHead5P.challenge_distr); first
        by wp; rnd; skip => /#.
      sp; seq 1 1 : (#pre /\ ={rss}); first by call (_:true); skip => /#.
      if{2}; last first.
        rcondf{1} 9; first move => &m.
          wp; do (call (_ : true); first by if => //); call (_ : true); wp; skip => *;
rewrite /valid_rand_prover /= /#.
        rcondf{2} 3; first move => &m.
          by wp; call (_ : true); wp; skip; auto.
        by rnd; wp; do call{1} ccsrandp_ll; wp; call{1} rmpc_ll; call{2} rmpc_ll; wp; skip.
      sp; seq 1 1 : (#pre /\ rmpc{1} = r{2}); first
        by call (_ : true); skip => /> *; exists ([]) ([]).
      case (valid_rands c{2} r{2}); last first.
        rcondf{2} 1; first by move => &m; wp; skip => /#. 
        rcondf{1} 7; first move => &m. 
          wp; do (call (_ : true); first by if => //); wp; skip; auto.
          by smt().
        by rnd; wp; do call{1} ccsrandp_ll; wp; skip; auto.
      rcondt{2} 1; first move => &m; skip; progress.
rewrite /valid_inputs.
exists rss{hr} x{hr}.
rewrite H3 H1 /=.
rewrite /sinput /input.
have ->: map (fun (pid : pid_t) => (pid, (oget (assoc (mk_inputs aux{hr} (share rss{hr} x{hr})) pid)).`2))
  ProtocolFunctionality.pid_set = 
map
  (fun (pid : pid_t) =>
     (pid, oget (assoc (share rss{hr} x{hr}) pid))) ProtocolFunctionality.pid_set.
rewrite -eq_in_map => pid; progress.
by rewrite map_assoc //=.
have : unzip1 (share rss{hr} x{hr}) = pid_set.
smt.
move=> H5.
rewrite (eq_assoc_map (share rss{hr} x{hr})).
smt.
rewrite H5.
rewrite -eq_in_map => pid; progress.
by rewrite !map_assoc //=.
smt().
      inline Privacy.RealEvaluator.eval; sp.
      inline F(D, RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV).guess; sp.
      seq 5 5 : (#pre /\ RP.rcsi{1} = rcsi{2} /\ RP.rcsj{1} = rcsj{2} /\
                         RP.rcsk{1} = rcsk{2} /\ RP.rcsl{1} = rcsl{2} /\
                         RP.rcsm{1} = rcsm{2}); first
        by do call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip; progress;
          by move : H0 H1 H3; case (F.i{2}); case (F.j{2}); smt(challenge_distr_diff).
      sp; if; last by wp; rnd.
        progress; rewrite /valid_rand_prover /=.
        move : H0 H1 H3.
        by case (F.i{2}); case (F.j{2}) => //=; smt(@List challenge_distr_diff).
        move : H0 H1 H3.
        by case (F.i{2}); case (F.j{2}) => //=; smt(@List challenge_distr_diff).
        move : H0 H1 H3.
        by case (F.i{2}); case (F.j{2}) => //=; smt(@List challenge_distr_diff).
        move : H0 H1 H3.
        by case (F.i{2}); case (F.j{2}) => //=; smt(@List challenge_distr_diff).
        move : H0 H1 H3.
        by case (F.i{2}); case (F.j{2}) => //=; smt(@List challenge_distr_diff).
      inline RealEvaluator4(MV).eval; sp.
      seq 1 1 : (#pre /\ ={ch}).
        call (_ : true); skip; progress; last by smt().
          rewrite -eq_in_map => pid H8; rewrite /sinput /input /view /= !map_assoc //=;
            first 2 by smt().
          rewrite !map_assoc // /tuple5_to_list /= /assemble /=; move : H1 H2 H4.
            by case (F.i{2}); case (F.j{2}) => //=;
              (progress; move : H8; case pid => //=; 
                (progress; rewrite ?assocP1 ?assocP2 ?assocP3 ?assocP4 ?assocP5 ?map_assoc //=; 
                  smt(@List challenge_distr_diff))).
      sp 2 1; if => //; last first.
        wp; call (_ : true); wp; skip; progress.
        rewrite /mk_inputs /sinput /input /pid_set /pid_mpc_set /= assocP1 assocP2 assocP3 assocP4 assocP5 /=.
        have E: [(P1, oget (assoc (share rss{2} x{2}) P1)); (P2, oget (assoc (share rss{2} x{2}) P2)); (P3, oget (assoc (share rss{2} x{2}) P3)); (P4, oget (assoc (share rss{2} x{2}) P4)); (P5, oget (assoc (share rss{2} x{2}) P5))] = map (fun pid => (pid, oget (assoc (share rss{2} x{2}) pid))) pid_set by rewrite /pid_set /pid_mpc_set /=.
        move : (eq_assoc_map (share rss{2} x{2})).
        by rewrite E unzip1_share; smt(pid_set_uniq SS5.correct).
      wp; call (_ : true); wp; skip; progress.
      have E: [(P1, oget (assoc (share rss{2} x{2}) P1)); (P2, oget (assoc (share rss{2} x{2}) P2)); (P3, oget (assoc (share rss{2} x{2}) P3)); (P4, oget (assoc (share rss{2} x{2}) P4)); (P5, oget (assoc (share rss{2} x{2}) P5))] = map (fun pid => (pid, oget (assoc (share rss{2} x{2}) pid))) pid_set by rewrite /pid_set /pid_mpc_set /=.
        * rewrite /mk_inputs /sinput /input /pid_set /pid_mpc_set /= 
                  assocP1 assocP2 assocP3 assocP4 assocP5 /=.
          move : (eq_assoc_map (share rss{2} x{2})).
          by rewrite E unzip1_share; smt(pid_set_uniq SS5.correct).
        * rewrite -eq_in_map => pid; progress => //.
          rewrite /sinput /input /view /= !map_assoc //=; first 2 by smt().
          rewrite !map_assoc // /tuple5_to_list /= /assemble /=; move : H1 H2 H4.
          by case (F.i{2}); case (F.j{2}) => //=; 
              (progress; move : H8; case pid => //=; 
                (progress; rewrite ?assocP1 ?assocP2 ?assocP3 ?assocP4 ?assocP5 ?map_assoc //=; 
                  smt(@List challenge_distr_diff))).
         * rewrite -eq_in_map => pid; progress.
          rewrite /sinput /input /view /= !map_assoc //=; first 2 by smt().
          rewrite !map_assoc // /tuple5_to_list /= /assemble /=; move : H1 H2 H4.
          by case (F.i{2}); case (F.j{2}) => //=; 
              (progress; move : H8; case pid => //=; 
                (progress; rewrite ?assocP1 ?assocP2 ?assocP3 ?assocP4 ?assocP5 ?map_assoc //=; 
                  smt(@List challenge_distr_diff))).
        * rewrite /response /= /get_party_committed_view /= /view /input /rand /trace /=.
          rewrite !map_assoc //=; first 6 by smt(challenge_distr_diff).
          rewrite !map_assoc //=; first 2 by smt(challenge_distr_diff).
          rewrite !map_assoc //=; first 2 by smt(challenge_distr_diff).
          move : H1 H2 H4; rewrite /tuple5_to_list /= /assemble /=.
          by case (F.i{2}); case (F.j{2}) => //= /> *;
            rewrite ?assocP1 ?assocP2 ?assocP3 ?assocP4 ?assocP5 ?map_assoc //=; 
              smt(@List challenge_distr_diff).
    qed.

    local lemma real5_privacy_ideal : 
      equiv [ GameReal5.main ~ 
              Privacy.GameIdeal(F(D,RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV), RMPC, S_MPC).main :
              ={glob D, glob RSS, glob RMPC, glob S_MPC, glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5,
                glob MV} /\ c{2} = relc /\ x{1} = aux{2} /\ valid_secret w{1} /\ w{1} = x{2}
                ==> ={res} ].
    proof.
      proc.
      inline F(D, RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV).choose.
      inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
      sp; seq 1 1 : (#pre /\ RP.i{1} = F.i{2} /\ RP.j{1} = F.j{2} /\
                    (F.i, F.j){2} \in InTheHead5P.challenge_distr); first
        by wp; rnd; skip => /#.
      sp; seq 1 1 : (#pre /\ ={rss}); first by call (_:true); skip => /#.
      if{2}; last first.
        rcondf{1} 9; first move => &m.
          wp; do (call (_ : true); first by if => //); call (_ : true); wp; skip; auto.
          by rewrite /valid_rand_prover; smt().
        rcondf{2} 3; first move => &m.
          by call (_ : true); wp; skip; auto.
        by rnd; wp; do call{1} ccsrandp_ll; wp; call{1} rmpc_ll; call{2} rmpc_ll; wp; skip.
      sp; seq 1 1 : (#pre /\ rmpc{1} = r{2}); first
        by call (_ : true); skip => /> *; exists ([]) ([]).
      case (valid_rands c{2} r{2}); last first.
        rcondf{2} 1; first by move => &m; skip => /> /#. 
        rcondf{1} 7; first move => &m. 
          wp; do (call (_ : true); first by if => //); wp; skip; auto.
          by rewrite /valid_rand_prover; smt().
        by rnd; wp; do call{1} ccsrandp_ll; wp; skip; auto.
      rcondt{2} 1; first move => &m; skip; progress.
rewrite /valid_inputs.
exists rss{hr} x{hr}.
rewrite H3 H1 /=.
rewrite /sinput /input.
have ->: map (fun (pid : pid_t) => (pid, (oget (assoc (mk_inputs aux{hr} (share rss{hr} x{hr})) pid)).`2))
  ProtocolFunctionality.pid_set = 
map
  (fun (pid : pid_t) =>
     (pid, oget (assoc (share rss{hr} x{hr}) pid))) ProtocolFunctionality.pid_set.
rewrite -eq_in_map => pid; progress.
by rewrite map_assoc //=.
have : unzip1 (share rss{hr} x{hr}) = pid_set.
smt.
progress.
rewrite (eq_assoc_map (share rss{hr} x{hr})).
smt.
rewrite H5.
rewrite -eq_in_map => pid; progress.
by rewrite !map_assoc //=.
smt().
      inline Privacy.IdealEvaluator(S_MPC).eval; sp.
      inline F(D, RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV).guess; sp.
      sp. swap{2} [8..12]-7.
      seq 5 5 : (#pre /\ RP.rcsi{1} = rcsi{2} /\ RP.rcsj{1} = rcsj{2} /\
                         RP.rcsk{1} = rcsk{2} /\ RP.rcsl{1} = rcsl{2} /\
                         RP.rcsm{1} = rcsm{2}); first by
        do call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip; progress;
          by move : H H0 H2; case (F.i{2}); case (F.j{2}); smt(challenge_distr_diff).
      sp; if{1}; last first. 
        rcondf{2} 9; first move => &m; wp; call (_ : true); skip; progress.
        move : H5; rewrite /valid_rand_prover /=; move : H4.
        rewrite /tuple5_to_list /assemble /=.
        move : H H0 H2; case (F.i{hr}); case (F.j{hr}) => //=; (progress; smt(@List challenge_distr_diff)).
        by wp; rnd; wp; call{2} s_mpc_ll; skip.
      inline RealEvaluator5(MV, S_MPC).eval; sp.
      seq 1 1 : (#pre /\ vsc{1} = vsc0{2}); first 
        call (_ : true); skip; progress. by exists ([]) ([]).
      sp; if{2}; last by exfalso => /#. 
      sp; seq 1 1 : (#pre /\ ={ch}).
        call (_ : true); skip; progress; last by smt().
          by rewrite -eq_in_map => pid; progress; rewrite /sinput /input /view /= !map_assoc //=;
            first by smt().
      sp 2 1; if => //; last first.
        wp; call (_ : true); wp; skip; progress.
        have E: [(P1, oget (assoc (share rss{2} x{2}) P1)); (P2, oget (assoc (share rss{2} x{2}) P2)); (P3, oget (assoc (share rss{2} x{2}) P3)); (P4, oget (assoc (share rss{2} x{2}) P4)); (P5, oget (assoc (share rss{2} x{2}) P5))] = map (fun pid => (pid, oget (assoc (share rss{2} x{2}) pid))) pid_set by rewrite /pid_set /pid_mpc_set /=.
        rewrite /mk_inputs /sinput /input /pid_set /pid_mpc_set /= assocP1 assocP2 assocP3 assocP4 assocP5 /=.
        move : (eq_assoc_map (share rss{2} x{2})).
        by rewrite E unzip1_share; smt(pid_set_uniq SS5.correct).
      wp; call (_ : true); wp; skip; progress.
      have E: [(P1, oget (assoc (share rss{2} x{2}) P1)); (P2, oget (assoc (share rss{2} x{2}) P2)); (P3, oget (assoc (share rss{2} x{2}) P3)); (P4, oget (assoc (share rss{2} x{2}) P4)); (P5, oget (assoc (share rss{2} x{2}) P5))] = map (fun pid => (pid, oget (assoc (share rss{2} x{2}) pid))) pid_set by rewrite /pid_set /pid_mpc_set /=.
        * rewrite /mk_inputs /sinput /input /pid_set /pid_mpc_set /= 
                  assocP1 assocP2 assocP3 assocP4 assocP5 /=.
          move : (eq_assoc_map (share rss{2} x{2})).
          by rewrite E unzip1_share; smt(pid_set_uniq SS5.correct).
        * rewrite -eq_in_map => pid; progress.
          rewrite /sinput /input /view /= !map_assoc //=; first by smt().
          rewrite /tuple5_to_list /= /assemble /=; move : H H0 H2.
          by case (F.i{2}); case (F.j{2}) => //=; smt(@List challenge_distr_diff).
          rewrite /response /= /get_party_committed_view /= /view /input /rand /trace /=.
          move : H H0 H2; rewrite /tuple5_to_list /= /assemble /=.
          by case (F.i{2}); case (F.j{2}) => //=; smt(@List challenge_distr_diff).
    qed.

    local lemma adv_privacy_hop4 &m w x : 
      valid_secret w =>
      Pr[GameReal4.main(w,x) @ &m : res] - Pr[GameReal5.main(w,x) @ &m : res] <= 
      Pr[Privacy.GameReal(F(D,RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV), RMPC).main(relc, w, x) @ &m : res] -
      Pr[Privacy.GameIdeal(F(D,RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV), RMPC, S_MPC).main(relc, w,  x) @ &m : res].
    proof.
      move => H.
      have ->: Pr[GameReal4.main(w,x) @ &m : res] = 
              Pr[Privacy.GameReal(F(D,RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV), RMPC).main(relc, w,  x) @ &m : res].
        by byequiv real4_privacy_real => /#.
      have ->: Pr[GameReal5.main(w,x) @ &m : res] = 
              Pr[Privacy.GameIdeal(F(D,RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV), RMPC, S_MPC).main(relc, w, x) @ &m : res] 
        by byequiv real5_privacy_ideal => /= /#.
      by done.
    qed.

    local lemma real5_ss_real : 
      equiv [ GameReal5.main ~ 
              SecretSharingSchemeSecurity.GameReal(G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC), RSS).main :
              ={glob D, glob RSS, glob RMPC, glob S_MPC, glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5,
                glob MV} /\ x{1} = aux{2} /\ w{1} = s{2} /\ valid_secret w{1} ==> ={res} ].
    proof.
      proc.
      inline G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC).choose.
      inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
      sp; seq 1 1 : (#pre /\ RP.i{1} = G.i{2} /\ RP.j{1} = G.j{2} /\
                    (G.i, G.j){2} \in InTheHead5P.challenge_distr); first
        by wp; rnd; skip => /#.
      sp; seq 1 1 : (#pre /\ rss{1} = r{2}); first by call (_:true). 
      if{2}; last first.
        rcondf{1} 9; first move => &m.
          wp; do (call (_ : true); first by if => //); call (_ : true); wp; skip; progress.
          
move : H3.
have ->: ((valid_rand r{m} s{m})%SS /\
   (valid_corrupted_set [G.i{m}; G.j{m}])%SecretSharingSchemeSecurity) = 
((valid_rand r{m} s{m})%SS).
move : H2.
by elim (G.i{m}); elim (G.j{m}) => /=; smt(challenge_distr_diff).
move => H3.
by rewrite /valid_rand_prover; smt().

        by rnd; wp; do call{1} ccsrandp_ll; wp; call{1} rmpc_ll; wp; skip.
      inline SecretSharingSchemeSecurity.RealEvaluator.share.
      inline G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC).guess.
      sp; seq 1 1 : (#pre /\ ={rmpc}); first by call (_ : true); skip => /#.
      swap{2} [5..10] -4.
      seq 5 5 : (#pre /\ RP.rcsi{1} = rcsi{2} /\ RP.rcsj{1} = rcsj{2} /\
                         RP.rcsk{1} = rcsk{2} /\ RP.rcsl{1} = rcsl{2} /\
                         RP.rcsm{1} = rcsm{2}); first by
        do call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip; progress;
          by move : H H0 H2; case (G.i{2}); case (G.j{2}); smt(challenge_distr_diff).
      sp; if{1}; last first.
        rcondf{2} 5; first move => &m; wp; call (_ : true); skip; progress.
          move : H5; rewrite /valid_rand_prover /=. 
          have ->: unzip1 (tuple5_to_list (assemble (G.i{hr}, rcsi{hr}) (G.j{hr}, rcsj{hr}) (RP.k{m}, rcsk{hr}) (RP.l{m}, rcsl{hr}) (RP.m{m}, rcsm{hr}))) = SS5.pid_set.
            rewrite /valid_rands /= /tuple5_to_list /= /assemble /=.
            by move : H H0 H2; case (G.i{hr}); case (G.j{hr}) => //=; smt(challenge_distr_diff).
          have ->: size (tuple5_to_list (assemble (G.i{hr}, rcsi{hr}) (G.j{hr}, rcsj{hr}) (RP.k{m}, rcsk{hr}) (RP.l{m}, rcsl{hr}) (RP.m{m}, rcsm{hr}))) = SS5.n.
            rewrite /valid_rands /= /tuple5_to_list /= /assemble /=.
            by move : H H0 H2; case (G.i{hr}); case (G.j{hr}) => //=; smt(challenge_distr_diff).
          by rewrite /valid_rands allP //=; smt().
        by wp; rnd; wp; call{2} s_mpc_ll; skip.
      inline RealEvaluator5(MV, S_MPC).eval.
      sp; seq 1 1 : (#pre /\ ={vsc}); first call (_ : true); skip; progress. 
        * by rewrite /input /= !map_assoc //= 1:/#.
        * rewrite /input /= !map_assoc //= 1:/#. 
rewrite /get_party_share /=.
smt(@List).
rewrite /relation.

case (exists (ss : (pid_t * share_t) list),
  s{2} = reconstruct ss /\
  in_rng_share ss /\
  let xs = mk_inputs aux{2} ss in
  let outs = f relc xs in all (fun (x : pid_t * bool) => x.`2) outs); last first.
rewrite existsN.
progress.
move : (H6 (share r{2} s{2})).
have <-: s{2} = reconstruct (share r{2} s{2}).
smt.
simplify.
have ->: in_rng_share (share r{2} s{2}).
rewrite /in_rng_share /=.
exists (r{2}) (s{2}).
have ->: valid_rand r{2} s{2} by smt().
by rewrite H1.
simplify.
rewrite allP.
rewrite forallN.
progress.
move : (good_circuit aux{2} s{2}).
progress.
move : (H9 (share r{2} s{2}) (share r{2} s{2})).
have <-: s{2} = InTheHead5P.SS.reconstruct (share r{2} s{2}).
smt.
simplify.
progress.
rewrite /output /=.
have : x2 \in f relc (mk_inputs aux{2} (share r{2} s{2})).
smt.
have : !x2.`2 by smt().
progress.
move : H11; rewrite allP.
progress.
move : (H11 (G.i{2}, oget (assoc (f relc (mk_inputs aux{2} (share r{2} s{2}))) G.i{2}))).
have ->: (G.i{2},
  oget
    (assoc (f relc (mk_inputs aux{2} (share r{2} s{2})))
       G.i{2})) \in
 f relc (mk_inputs aux{2} (share r{2} s{2})).
rewrite assoc_get_mem.
smt.
smt(challenge_mem_pid_set).
progress.
move : H7.
rewrite allP /output.
progress.
move : (H7 (G.i{2}, oget (assoc (f relc (mk_inputs aux{2} (share r{2} (reconstruct ss2)))) G.i{2}))).

have ->: (G.i{2},
  oget
    (assoc
       (f relc (mk_inputs aux{2} (share r{2} (reconstruct ss2)))) G.i{2})) \in
 f relc (mk_inputs aux{2} ss2).
move : (good_circuit aux{2} (reconstruct ss2)).
progress.
move : (H9 (share r{2} (reconstruct ss2)) ss2).
have ->: InTheHead5P.SS.reconstruct (share r{2} (reconstruct ss2)) = reconstruct ss2.
smt.
simplify.
have ->: (InTheHead5P.SS.reconstruct ss2) = reconstruct ss2 by smt().
progress.
rewrite H10.
rewrite assoc_get_mem.
smt(challenge_mem_pid_set).
simplify.
progress.
rewrite H8 => />.
have ->: exists (ss : (pid_t * share_t) list),
  reconstruct ss2 = reconstruct ss /\
  in_rng_share ss /\
  all (fun (x : pid_t * bool) => x.`2) (f relc (mk_inputs aux{2} ss)).
exists ss2.
rewrite allP.
smt().
done.

rewrite /relation.

case (exists (ss : (pid_t * share_t) list),
  s{2} = reconstruct ss /\ in_rng_share ss /\
  let xs = mk_inputs aux{2} ss in
  let outs = f relc xs in all (fun (x : pid_t * bool) => x.`2) outs); last first.
rewrite existsN.
progress.
move : (H6 (share r{2} s{2})).
have <-: s{2} = reconstruct (share r{2} s{2}).
smt.
simplify.
have ->: in_rng_share (share r{2} s{2}) by smt().
rewrite allP /=.
rewrite forallN.
progress.
move : (good_circuit aux{2} s{2}).
progress.
move : (H9 (share r{2} s{2}) (share r{2} s{2})).
have <-: s{2} = InTheHead5P.SS.reconstruct (share r{2} s{2}).
smt.
simplify.
progress.
rewrite /output /=.
have : x2 \in f relc (mk_inputs aux{2} (share r{2} s{2})).
smt.
have : !x2.`2 by smt().
progress.
move : H11; rewrite allP.
progress.
move : (H11 (G.j{2}, oget (assoc (f relc (mk_inputs aux{2} (share r{2} s{2}))) G.j{2}))).
have ->: (G.j{2},
  oget
    (assoc (f relc (mk_inputs aux{2} (share r{2} s{2})))
       G.j{2})) \in
 f relc (mk_inputs aux{2} (share r{2} s{2})).
rewrite assoc_get_mem.
smt.
smt(challenge_mem_pid_set).
progress.
move : H7.
rewrite allP /output.
progress.
move : (H7 (G.j{2}, oget (assoc (f relc (mk_inputs aux{2} (share r{2} (reconstruct ss2)))) G.j{2}))).

have ->: (G.j{2},
  oget
    (assoc
       (f relc (mk_inputs aux{2} (share r{2} (reconstruct ss2)))) G.j{2})) \in
 f relc (mk_inputs aux{2} ss2).
move : (good_circuit aux{2} (reconstruct ss2)).
progress.
move : (H9 (share r{2} (reconstruct ss2)) ss2).
have ->: InTheHead5P.SS.reconstruct (share r{2} (reconstruct ss2)) = reconstruct ss2.
smt.
have ->: InTheHead5P.SS.reconstruct ss2 = reconstruct ss2.
smt().
simplify.
progress.
rewrite H10.
rewrite assoc_get_mem.
smt(challenge_mem_pid_set).

simplify.
progress.
rewrite H8.
have ->: exists (ss : (pid_t * share_t) list),
  reconstruct ss2 = reconstruct ss /\
  in_rng_share ss /\
  all (fun (x : pid_t * bool) => x.`2) (f relc (mk_inputs aux{2} ss)).
exists ss2.
rewrite allP.
smt().
done.

      rcondt{2} 4; first by move => &m; wp; skip; progress;
        (move : H5; rewrite /valid_rand_prover /=;
        by move : H H0 H2; case (G.i{hr}); case (G.j{hr}) => //=; smt(challenge_distr_diff)).
      sp; seq 1 1 : (#pre /\ ={ch}).
        call (_ : true); skip; progress.
          by rewrite -eq_in_map => pid; progress; rewrite /sinput /input /view /= !map_assoc //=;
            first by smt().
      sp 2 1; if => //; last by wp; call (_ : true); wp; skip. 
      wp; call (_ : true); wp; skip; progress.
        * rewrite -eq_in_map => pid; progress.
          by rewrite /sinput /input /view /= !map_assoc //=; first by smt().
          rewrite /tuple5_to_list /= /assemble /=; move : H H0 H2.
          by case (G.i{2}); case (G.j{2}) => //=; smt(@List challenge_distr_diff).
        * rewrite /response /= /get_party_committed_view /= /view /input /rand /trace /=.
          by rewrite !map_assoc //=; first 5 by smt(challenge_distr_diff).
    qed.


    local lemma ideal_ss_ideal : 
      equiv [ GameIdeal(D, RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5), MV, Simulator(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5, MV, S_MPC, S_SS)).main ~ 
              SecretSharingSchemeSecurity.GameIdeal(G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC), RSS, S_SS).main :
              ={glob D, glob RSS, glob RMPC, glob S_MPC, glob S_SS, glob RCS1, glob RCS2, glob RCS3, glob RCS4, glob RCS5,
                glob MV} /\ relation w{1} x{1} /\ x{1} = aux{2} /\ w{1} = s{2} /\ valid_secret w{1} ==> ={res} ].
    proof.
      proc.
      inline G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC).choose.
      inline RP(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5).gen.
      sp; seq 1 1 : (#pre /\ RP.i{1} = G.i{2} /\ RP.j{1} = G.j{2} /\
                    (G.i, G.j){2} \in InTheHead5P.challenge_distr); first
        by wp; rnd; skip => /#.
      sp; seq 1 1 : (#pre /\ rss{1} = r{2}); first by call (_:true). 
      if{2}; last first.
        rcondf{1} 9; first move => &m.
          wp; do (call (_ : true); first by if => //); call (_ : true); wp; skip; progress.

move : H4.
have ->: ((valid_rand r{m} s{m})%SS /\
   (valid_corrupted_set [G.i{m}; G.j{m}])%SecretSharingSchemeSecurity) = 
((valid_rand r{m} s{m})%SS).
move : H3.
by elim (G.i{m}); elim (G.j{m}) => /=; smt(challenge_distr_diff).
move => H4.
by rewrite /valid_rand_prover; smt(). 
        by rnd; wp; do call{1} ccsrandp_ll; wp; call{1} rmpc_ll; wp; skip.
      inline SecretSharingSchemeSecurity.IdealEvaluator(S_SS).share.
      inline G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC).guess.
      inline IdealEvaluator(MV, Simulator(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC, S_SS)).eval.
      inline Simulator(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC, S_SS).gen_commitment.
      inline Simulator(RSS, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC, S_SS).gen_response.
      sp; swap{2} 6-5; seq 1 1 : (#pre /\ ={rmpc}); first by call (_ : true); skip => /#.
      swap{2} 3-2. swap{2} 5-3. sp. swap{2} [8..12] -7.
      seq 5 5 : (#pre /\ RP.rcsi{1} = rcsi{2} /\ RP.rcsj{1} = rcsj{2} /\
                         RP.rcsk{1} = rcsk{2} /\ RP.rcsl{1} = rcsl{2} /\
                         RP.rcsm{1} = rcsm{2}); first by
        do call (csrandp_equiv RCS1 RCS2 RCS3 RCS4 RCS5); skip; progress;
          by move : H H0 H2; case (G.i{2}); case (G.j{2}); smt(challenge_distr_diff).
      sp; if{1}; last first.
        rcondf{2} 9; first move => &m; wp; call (_ : true); wp; call (_ : true); skip; progress.
          move : H6; rewrite /valid_rand_prover /=. 
          have ->: InTheHead5P.SS.valid_rand r{hr} s{hr} by smt().
          have ->: unzip1 (tuple5_to_list (assemble (G.i{hr}, rcsi{hr}) (G.j{hr}, rcsj{hr}) (RP.k{m}, rcsk{hr}) (RP.l{m}, rcsl{hr}) (RP.m{m}, rcsm{hr}))) = SS5.pid_set.
            rewrite /valid_rands /= /tuple5_to_list /= /assemble /=.
            by move : H H0 H3; case (G.i{hr}); case (G.j{hr}) => //=; smt(challenge_distr_diff).
          have ->: size (tuple5_to_list (assemble (G.i{hr}, rcsi{hr}) (G.j{hr}, rcsj{hr}) (RP.k{m}, rcsk{hr}) (RP.l{m}, rcsl{hr}) (RP.m{m}, rcsm{hr}))) = SS5.n.
            rewrite /valid_rands /= /tuple5_to_list /= /assemble /=.
            by move : H H0 H3; case (G.i{hr}); case (G.j{hr}) => //=; smt(challenge_distr_diff).
          by rewrite /valid_rands allP //=.
        by wp; rnd; wp; call{2} s_mpc_ll; wp; call{2} s_ss_ll; skip.
      sp; seq 1 1 : (#pre /\ xsc{1} = ssc{2}); first by call (_ : true); skip.
      sp. seq 1 1 : (#pre /\ ={vsc}); first by call (_ : true); skip => /#.
      sp; rcondt{1} 1; first by move => &m; skip.
      rcondt{2} 1; first by move => &m; wp; skip; progress;
        (move : H6; rewrite /valid_rand_prover /=;
        by move : H H0 H3; case (G.i{hr}); case (G.j{hr}) => //=; smt(challenge_distr_diff)).
      sp; seq 1 1 : (#pre /\ ={ch}).
        call (_ : true); skip; progress.
          by rewrite -eq_in_map => pid; progress; rewrite /sinput /input /view /= !map_assoc //=;
            first by smt().
      sp 4 1; if => //; last by wp; call (_ : true); wp; skip. 
      wp; call (_ : true); wp; skip; progress.
        * rewrite /accepting_conversation /InTheHead.check.
          * rewrite /response /= /get_party_committed_view /= /view /input /rand /trace /=.
          rewrite -eq_in_map => pid; progress.
          by rewrite /sinput /input /view /= !map_assoc //=; first by smt().
          by move : H H0 H3; case (G.i{2}); case (G.j{2}) => //=; smt(challenge_distr_diff).

          * rewrite /response /= /get_party_committed_view /= /view /input /rand /trace /=.
          by rewrite !map_assoc //=; first 5 by smt(challenge_distr_diff).
    qed.

    local lemma adv_ss_hop5 &m w x : 
      valid_secret w => relation w x =>
      Pr[GameReal5.main(w,x) @ &m : res] - Pr[GameIdeal(D, RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5), MV, Simulator(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5, MV, S_MPC, S_SS)).main(w,x) @ &m : res] <= 
      Pr[SecretSharingSchemeSecurity.GameReal(G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC), RSS).main(x,w) @ &m : res] -
      Pr[SecretSharingSchemeSecurity.GameIdeal(G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC), RSS, S_SS).main(x,w) @ &m : res].
    proof.
      move => H H0.
      have ->: Pr[GameReal5.main(w,x) @ &m : res] = 
              Pr[SecretSharingSchemeSecurity.GameReal(G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC), RSS).main(x,w) @ &m : res].
        by byequiv real5_ss_real => /#.
      have ->: Pr[GameIdeal(D, RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5), MV, Simulator(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5, MV, S_MPC, S_SS)).main(w,x) @ &m : res] = 
              Pr[SecretSharingSchemeSecurity.GameIdeal(G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC), RSS, S_SS).main(x,w) @ &m : res] 
        by byequiv ideal_ss_ideal => /= /#.
      by done.
    qed.

    local lemma zero_knowledge &m w x : 
      valid_secret w => relation w x =>
      Pr[GameReal1.main(w,x) @ &m : res] -
      Pr[GameIdeal(D, RP(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5), MV, Simulator(RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5, MV, S_MPC, S_SS)).main(w,x) @ &m : res] <=
        (* Hiding *)
        (Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       B(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game(((w,x), witness,true),true) @ &m : res] - 
      Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       B(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game(((w,x),witness,true),false) @ &m : !res]) +
        (* Hiding *)
        (Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       C(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game(((w,x), witness,true),true) @ &m : res] - 
      Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       C(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game(((w,x),witness,true),false) @ &m : !res]) +
        (* Hiding *)
        (Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       E(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game(((w,x), witness,true),true) @ &m : res] - 
      Pr[Hiding.Game(AllCSRand(RCS1, RCS2, RCS3, RCS4, RCS5),
                       E(D,RSS,RMPC,RCS1,RCS2,RCS3,RCS4,RCS5,MV)).game(((w,x),witness,true),false) @ &m : !res]) +
        (* Privacy *)
        (Pr[Privacy.GameReal(F(D,RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV), RMPC).main(relc, w, x) @ &m : res] -
      Pr[Privacy.GameIdeal(F(D,RSS, RCS1, RCS2, RCS3, RCS4, RCS5, MV), RMPC, S_MPC).main(relc, w, x) @ &m : res]) +
        (* Secret sharing *)
        (Pr[SecretSharingSchemeSecurity.GameReal(G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC), RSS).main(x,w) @ &m : res] -
      Pr[SecretSharingSchemeSecurity.GameIdeal(G(D, RMPC, RCS1, RCS2, RCS3, RCS4, RCS5, MV, S_MPC), RSS, S_SS).main(x,w) @ &m : res]).
    proof.
      move => H.
      move : (adv_commitment_hop1 &m (w,x)).
      move : (adv_commitment_hop2 &m (w,x)).
      move : (adv_commitment_hop3 &m (w,x)).
      move : (adv_privacy_hop4 &m w x).
      move : (adv_ss_hop5 &m w x).
      by rewrite !H /= => /#.
    qed.

  end section ZeroKnowledge.

end InTheHead5P.
