require import AllCore List Int IntDiv List Distr.

from General require import PrimeField Utils ListExt FieldPolynomial.

from SecretSharing require import Shamir.
from MPC require import AProtocol ProtocolWeak.
from Circuit require import ArithmeticCircuit.
from Functionalities require import ArithmeticProtocolFunctionality.
from ArithmeticProtocol require import ArithmeticProtocol.
from BGW require import Addition Multiplication SMultiplication BGWInput.

theory BGWGate.

  clone import BGWMultiplication.
  import HMShamir.
  clone import BGWAddition with
    op Shamir.n = HMShamir.SecretSharingScheme.n,
    op Shamir.t = HMShamir.t,
    op Shamir.pid_set = pid_set,
    op Shamir.valid_secret = HMShamir.valid_secret,
    op Shamir.valid_rand = HMShamir.valid_rand,
    op Shamir.share = HMShamir.share,
    op Shamir.public_encoding = HMShamir.public_encoding,
    op Shamir.pub_reconstruct = HMShamir.pub_reconstruct,
    op Shamir.reconstruct = HMShamir.reconstruct,
    op Shamir.get_party_share = HMShamir.get_party_share.
  clone import BGWSMultiplication with
    op Shamir.n = HMShamir.n,
    op Shamir.t = HMShamir.t,
    op Shamir.pid_set = pid_set,
    op Shamir.valid_secret = HMShamir.valid_secret,
    op Shamir.valid_rand = HMShamir.valid_rand,
    op Shamir.share = HMShamir.share,
    op Shamir.public_encoding = HMShamir.public_encoding,
    op Shamir.pub_reconstruct = HMShamir.pub_reconstruct,
    op Shamir.reconstruct = HMShamir.reconstruct,
    op Shamir.get_party_share = HMShamir.get_party_share.
  clone import BGWInput with 
    op n = HMShamir.n,
    op t = HMShamir.t,
    op Shamir.pid_set = pid_set,
    op Shamir.valid_secret = HMShamir.valid_secret,
    op Shamir.valid_rand = HMShamir.valid_rand,
    op Shamir.share = HMShamir.share,
    op Shamir.public_encoding = HMShamir.public_encoding,
    op Shamir.pub_reconstruct = HMShamir.pub_reconstruct,
    op Shamir.reconstruct = HMShamir.reconstruct,
    op Shamir.get_party_share = HMShamir.get_party_share.
  clone import ArithmeticProtocol with theory SecretSharingScheme = HMShamir.SecretSharingScheme,
(*    op SecretSharingScheme.n = HMShamir.n,
    op SecretSharingScheme.t = HMShamir.t,
    type SecretSharingScheme.pid_t = pid_t,
    op SecretSharingScheme.pid_set = pid_set,
    op SecretSharingScheme.valid_secret = HMShamir.valid_secret,
    type SecretSharingScheme.share_t = HMShamir.share_t,
    type SecretSharingScheme.rand_t = HMShamir.rand_t,
    op SecretSharingScheme.valid_rand = HMShamir.valid_rand,
    op SecretSharingScheme.share = HMShamir.share,
    op SecretSharingScheme.public_encoding = HMShamir.public_encoding,
    op SecretSharingScheme.pub_reconstruct = HMShamir.pub_reconstruct,
    op SecretSharingScheme.reconstruct = HMShamir.reconstruct,
    op SecretSharingScheme.get_party_share = HMShamir.get_party_share,*)

    theory AdditionGate = BGWAddition.AdditionGate,
    theory MultiplicationGate = BGWMultiplication.MultiplicationGate,
    theory SMultiplicationGate = BGWSMultiplication.SMultiplicationGate,
    theory InputGate = BGWInput.InputGate
  proof valid_secret_add, valid_secret_mul, 
        ArithmeticProtocolFunctionality.SecretSharingScheme.n_pos,
        ArithmeticProtocolFunctionality.SecretSharingScheme.t_pos,
        ArithmeticProtocolFunctionality.SecretSharingScheme.pid_set_size,
        ArithmeticProtocolFunctionality.SecretSharingScheme.pid_set_uniq,
        ArithmeticProtocolFunctionality.SecretSharingScheme.correct,
        ArithmeticProtocolFunctionality.SecretSharingScheme.size_share,
        ArithmeticProtocolFunctionality.SecretSharingScheme.unzip1_share,
        ArithmeticProtocolFunctionality.SecretSharingScheme.public_encoding_correct,
        ArithmeticProtocolFunctionality.SecretSharingScheme.size_public_encoding,
        ArithmeticProtocolFunctionality.SecretSharingScheme.unzip1_public_encoding,
        ArithmeticProtocolFunctionality.SecretSharingScheme.public_encoding_inj,
        ArithmeticProtocolFunctionality.SecretSharingScheme.public_encoding_reconstruct,
        ArithmeticProtocolFunctionality.SecretSharingScheme.public_encoding_rand,
        ArithmeticProtocolFunctionality.ProtocolFunctionality.n_pos,
        ArithmeticProtocolFunctionality.ProtocolFunctionality.t_pos,
        ArithmeticProtocolFunctionality.ProtocolFunctionality.pid_set_uniq,
        ArithmeticProtocolFunctionality.ProtocolFunctionality.pid_set_size.
  realize valid_secret_add by rewrite /valid_secret /=.
  realize valid_secret_mul by rewrite /valid_secret /=.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.n_pos by apply n_pos.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.t_pos by smt(n_pos t_pos).
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.pid_set_size by apply pid_set_size.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.pid_set_uniq by apply pid_set_uniq.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.correct by move : HMShamir.SecretSharingScheme.correct => /#.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.size_share by move : HMShamir.SecretSharingScheme.size_share => /#.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.unzip1_share by move : HMShamir.SecretSharingScheme.unzip1_share => /#.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.public_encoding_correct by move : HMShamir.SecretSharingScheme.public_encoding_correct => /#.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.size_public_encoding by move : HMShamir.SecretSharingScheme.size_public_encoding => /#.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.unzip1_public_encoding by move : HMShamir.SecretSharingScheme.unzip1_public_encoding => /#.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.public_encoding_inj by move : HMShamir.SecretSharingScheme.public_encoding_inj => /#.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.public_encoding_reconstruct by move : HMShamir.SecretSharingScheme.public_encoding_reconstruct => /#.
  realize ArithmeticProtocolFunctionality.SecretSharingScheme.public_encoding_rand by move : HMShamir.SecretSharingScheme.public_encoding_rand => /#.
  realize ArithmeticProtocolFunctionality.ProtocolFunctionality.n_pos by apply n_pos.
  realize ArithmeticProtocolFunctionality.ProtocolFunctionality.t_pos by smt (n_pos t_pos).
  realize ArithmeticProtocolFunctionality.ProtocolFunctionality.pid_set_uniq by apply pid_set_uniq.
  realize ArithmeticProtocolFunctionality.ProtocolFunctionality.pid_set_size by apply pid_set_size.

  import ArithP.
  import ProtocolFunctionality.
  import ArithmeticProtocolFunctionality.
  import ArithmeticCircuit.
  import Circuit.

print SInputLT.

  op simulate_gates (gg : gates_t) (rs : rands_t) (xs : inputs_t) (cr : pid_t list) : poutputs_t * (pid_t * (ProtocolFunctionality.input_t * rand_t * gate_local_traces_t)) list =
    with gg = PInput w => 
      let gys = public_encoding (nth witness (ProtocolFunctionality.pinput (head witness cr) xs) w) in
      let gysc = map (fun pid => (pid, oget (assoc gys pid))) cr in
      let tr = map (fun pid => (pid, (ProtocolFunctionality.input pid xs, ArithP.rand pid rs, PInputLT (nth witness (ProtocolFunctionality.pinput (head witness cr) xs) w)))) cr in
      (gysc, tr)

      
    with gg = SInput w => 
      let ri = map (fun pid => (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w)))) ProtocolFunctionality.pid_set in

      let gxs = map (fun pid => (pid, ((), nth witness (ProtocolFunctionality.sinput pid xs) w))) cr in
      let (gys, gtr) = InpSec.simulator ri gxs cr in
      let tr = map (fun pid => (pid, (ProtocolFunctionality.input pid xs, ArithP.rand pid rs, SInputLT w (oget (assoc gtr pid)).`3))) cr in

      (gys, tr)

    with gg = Constant gid c => 
      let gys = public_encoding c in
      let gysc = map (fun pid => (pid, oget (assoc gys pid))) cr in
      let tr = map (fun pid => (pid, (ProtocolFunctionality.input pid xs, ArithP.rand pid rs, ConstantLT gid c))) cr in

      (gysc, tr)

    with gg = Addition gid wl wr => 
      let ra = map (fun pid => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) ProtocolFunctionality.pid_set in
      let (vwl, tl) = simulate_gates wl rs xs cr in
      let (vwr, tr) = simulate_gates wr rs xs cr in

      let gxs = map (fun pid => (pid, ((), (oget (assoc vwl pid), oget (assoc vwr pid))))) cr in

      let (gys, gtr) = AddSec.simulator ra gxs cr in
      let tr = map (fun pid => (pid, (ProtocolFunctionality.input pid xs, ArithP.rand pid rs, AdditionLT gid (oget (assoc gtr pid)).`3 (oget (assoc tl pid)).`3 (oget (assoc tr pid)).`3))) cr in

      (gys, tr)

    with gg = Multiplication gid wl wr => 
      let rm = map (fun pid => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) ProtocolFunctionality.pid_set in
      let (vwl, tl) = simulate_gates wl rs xs cr in
      let (vwr, tr) = simulate_gates wr rs xs cr in

      let gxs = map (fun pid => (pid, ((), (oget (assoc vwl pid), oget (assoc vwr pid))))) cr in

      let (gys, gtr) = MulSec.simulator rm gxs cr in
      let tr = map (fun pid => (pid, (ProtocolFunctionality.input pid xs, ArithP.rand pid rs, MultiplicationLT gid (oget (assoc gtr pid)).`3 (oget (assoc tl pid)).`3 (oget (assoc tr pid)).`3))) cr in

      (gys, tr)

    with gg = SMultiplication gid wl wr => 
      let rsm = map (fun pid => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) ProtocolFunctionality.pid_set in
      let (vwl, tl) = simulate_gates wl rs xs cr in
      let (vwr, tr) = simulate_gates wr rs xs cr in

      let gxs = map (fun pid => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) cr in

      let (gys, gtr) = SMulSec.simulator rsm gxs cr in
      let tr = map (fun pid => (pid, (ProtocolFunctionality.input pid xs, ArithP.rand pid rs, SMultiplicationLT gid (oget (assoc gtr pid)).`3 (oget (assoc tl pid)).`3 (oget (assoc tr pid)).`3))) cr in

      (gys, tr).

  op simulator (c : circuit_t) (xs : inputs_t) (rs : rands_t) (cr : pid_t list) : poutputs_t * (pid_t * (ProtocolFunctionality.input_t * rand_t * gate_local_traces_t)) list = 
    let (topo, gg) = c in
    simulate_gates gg rs xs cr.

  clone import WeakSecurity with
    theory Protocol <- ArithmeticProtocol.ArithP,
    op simulator = simulator.  

    type gate_rands_t =[ 
      | InputRands of BGWInput.InputGate.Gate.rands_t
      | AdditionRands of BGWAddition.AdditionGate.Gate.rands_t
      | MultiplicationRands of BGWMultiplication.MultiplicationGate.Gate.rands_t 
      | SMultiplicationRands of BGWSMultiplication.SMultiplicationGate.Gate.rands_t 
    ].
    op is_gate_rands_input (r : gate_rands_t) : bool =
      with r = InputRands ra => true
      with r = AdditionRands ra => false
      with r = MultiplicationRands rm => false
      with r = SMultiplicationRands rsm => false.
    op as_gate_rands_input (r : gate_rands_t) =
      with r = InputRands ra => ra
      with r = AdditionRands ra => witness
      with r = MultiplicationRands rm => witness
      with r = SMultiplicationRands rsm => witness.
    op is_gate_rands_addition (r : gate_rands_t) : bool =
      with r = InputRands ra => false
      with r = AdditionRands ra => true
      with r = MultiplicationRands rm => false
      with r = SMultiplicationRands rsm => false.
    op as_gate_rands_addition (r : gate_rands_t) =
      with r = InputRands ra => witness
      with r = AdditionRands ra => ra
      with r = MultiplicationRands rm => witness
      with r = SMultiplicationRands rsm => witness.
    op is_gate_rands_multiplication (r : gate_rands_t) : bool =
      with r = InputRands ra => false
      with r = AdditionRands ra => false
      with r = MultiplicationRands rm => true
      with r = SMultiplicationRands rsm => false.
    op as_gate_rands_multiplication (r : gate_rands_t) =
      with r = InputRands ra => witness
      with r = AdditionRands ra => witness
      with r = MultiplicationRands rm => rm
      with r = SMultiplicationRands rsm => witness.
    op is_gate_rands_smultiplication (r : gate_rands_t) : bool =
      with r = InputRands ra => false
      with r = AdditionRands ra => false
      with r = MultiplicationRands rm => false
      with r = SMultiplicationRands rsm => true.
    op as_gate_rands_smultiplication (r : gate_rands_t) =
      with r = InputRands ra => witness
      with r = AdditionRands ra => witness
      with r = MultiplicationRands rm => witness
      with r = SMultiplicationRands rsm => rsm.

    op get_local_rand (pid : pid_t) (r : gate_rands_t) : gate_rand_t =
      with r = InputRands ra => InputRand (BGWInput.rand pid ra)
      with r = AdditionRands ra => AdditionRand (BGWAddition.rand pid ra)
      with r = MultiplicationRands rm => MultiplicationRand (BGWMultiplication.rand pid rm)
      with r = SMultiplicationRands rsm => SMultiplicationRand (BGWSMultiplication.rand pid rsm).

    lemma as_local_rand_mul (pid : pid_t) (r : gate_rands_t) :
      is_gate_rands_multiplication r => 
      oget (assoc (as_gate_rands_multiplication r) pid) =
      as_gate_rand_multiplication (get_local_rand pid r).
    proof. by elim r => //=. qed.

    lemma as_local_rand_inp (pid : pid_t) (r : gate_rands_t) :
      is_gate_rands_input r => 
      oget (assoc (as_gate_rands_input r) pid) =
      as_gate_rand_input (get_local_rand pid r).
    proof. by elim r => //=. qed.

    module type RandParam_t (RAdd : AddSec.Rand_t) (RMul : MulSec.Rand_t) (RSMul : SMulSec.Rand_t) = {
      proc gen(c : circuit_t, aux : WeakSecurity.aux_t, cr : pid_t list) : (gid_t * gate_rands_t) list
    }.

    axiom rand_good (RP <: RandParam_t) c_ cr_ :
      equiv [ RP(BGWAddition.R, BGWMultiplication.R, BGWSMultiplication.R).gen ~
              RP(BGWAddition.R, BGWMultiplication.R, BGWSMultiplication.R).gen : 
                ={glob RP, glob BGWAddition.R, glob BGWMultiplication.R, glob BGWSMultiplication.R} /\
                ={c, aux, cr} /\ cr_ = cr{2} /\ c_ = c{2} /\ 
                  (forall pid, pid \in cr{2} => pid \in ProtocolFunctionality.pid_set)
                  ==> ={glob RP} /\ unzip1 res{1} = unzip1 res{2} /\ unzip1 res{1} = range (c_.`1.`1) (c_.`1.`1 + c_.`1.`2 + c_.`1.`4) /\
                      (forall gid, gid \in unzip1 res{1} => 
                                   (is_gate_rands_input (oget (assoc res{1} gid)) <=> 
                                    is_gate_rands_input (oget (assoc res{2} gid))) /\

                                   (is_gate_rands_addition (oget (assoc res{1} gid)) <=> 
                                    is_gate_rands_addition (oget (assoc res{2} gid))) /\

                                   (is_gate_rands_multiplication (oget (assoc res{1} gid)) <=> 
                                    is_gate_rands_multiplication (oget (assoc res{2} gid))) /\

                                   (is_gate_rands_smultiplication (oget (assoc res{1} gid)) <=> 
                                    is_gate_rands_smultiplication (oget (assoc res{2} gid))) /\

                                   (is_gate_rands_input (oget (assoc res{1} gid)) =>
                                     let rm = as_gate_rands_input (oget (assoc res{1} gid)) in
                                     let rsm = as_gate_rands_input (oget (assoc res{2} gid)) in

                                     unzip1 rm = ProtocolFunctionality.pid_set /\ unzip1 rm = unzip1 rsm /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       if pid \in cr_ then get_local_rand pid (oget (assoc res{1} gid)) = 
                                                           get_local_rand pid (oget (assoc res{2} gid))
                                       else  
                                        (forall x c c', x <> fzero => 
                                          eval x (update (oget (assoc rm pid)) 0 c) = 
                                          eval x (update (oget (assoc rsm pid)) 0 c'))) /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       oget (assoc rm pid) \in dpolynomial ProtocolFunctionality.t) /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       oget (assoc rsm pid) \in dpolynomial ProtocolFunctionality.t)) /\ 

                                   (is_gate_rands_addition (oget (assoc res{1} gid)) => 
                                     let ra = as_gate_rands_addition (oget (assoc res{1} gid)) in
                                     let rsa = as_gate_rands_addition (oget (assoc res{2} gid)) in
                                     ra = rsa /\ BGWAddition.valid_rands ra) /\
 
                                   (is_gate_rands_multiplication (oget (assoc res{1} gid)) =>
                                     let rm = as_gate_rands_multiplication (oget (assoc res{1} gid)) in
                                     let rsm = as_gate_rands_multiplication (oget (assoc res{2} gid)) in

                                     unzip1 rm = ProtocolFunctionality.pid_set /\ unzip1 rm = unzip1 rsm /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       if pid \in cr_ then get_local_rand pid (oget (assoc res{1} gid)) = 
                                                           get_local_rand pid (oget (assoc res{2} gid))
                                       else  
                                        (forall x c c', x <> fzero => 
                                          eval x (update (oget (assoc rm pid)) 0 c) = 
                                          eval x (update (oget (assoc rsm pid)) 0 c'))) /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       oget (assoc rm pid) \in dpolynomial ProtocolFunctionality.t) /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       oget (assoc rsm pid) \in dpolynomial ProtocolFunctionality.t)) /\ 

                                    (is_gate_rands_smultiplication (oget (assoc res{1} gid)) => 
                                      let rsm = as_gate_rands_smultiplication (oget (assoc res{1} gid)) in
                                      let rssm = as_gate_rands_smultiplication (oget (assoc res{2} gid)) in
                                      rsm = rssm /\ BGWSMultiplication.valid_rands rsm)) ].

    module R (RP : RandParam_t) = {
      proc gen(c : circuit_t, cr : pid_t list, aux : aux_t) : rands_t = {
        var grs, rs;
      
        grs <@ RP(BGWAddition.R, BGWMultiplication.R, BGWSMultiplication.R).gen(c, aux, cr);
        rs <- map (fun pid => (pid, map (fun gid => (gid, get_local_rand pid (oget (assoc grs gid)))) (range (c.`1.`1) (c.`1.`1 + c.`1.`2 + c.`1.`4)))) ProtocolFunctionality.pid_set;

        return rs;
      }
    }.

  section Security.

    declare module D : Distinguisher_t.
    declare module RP : RandParam_t{D}.

    lemma get_local_rand_inp (r : gate_rands_t) pid :
      pid \in ProtocolFunctionality.pid_set => 
      is_gate_rands_input r <=> is_gate_rand_input (get_local_rand pid r).
    proof. by move => H; elim r => //=. qed.

    lemma get_local_rand_add (r : gate_rands_t) pid :
      pid \in ProtocolFunctionality.pid_set => 
      is_gate_rands_addition r <=> is_gate_rand_addition (get_local_rand pid r).
    proof. by move => H; elim r => //=. qed.

    lemma get_local_rand_mul (r : gate_rands_t) pid :
      pid \in ProtocolFunctionality.pid_set => 
      is_gate_rands_multiplication r <=> is_gate_rand_multiplication (get_local_rand pid r).
    proof. by move => H; elim r => //=. qed.

    lemma get_local_rand_smul (r : gate_rands_t) pid :
      pid \in ProtocolFunctionality.pid_set => 
      is_gate_rands_smultiplication r <=> is_gate_rand_smultiplication (get_local_rand pid r).
    proof. by move => H; elim r => //=. qed.

    lemma rand_eq_inp r r' pid :
      is_gate_rands_input r => is_gate_rands_input r' =>
      as_gate_rands_input r = as_gate_rands_input r' =>
      get_local_rand pid r = get_local_rand pid r'.
    proof. by case r r' => //; progress; move : H; case r' => //. qed.

    lemma rand_eq_add r r' pid :
      is_gate_rands_addition r => is_gate_rands_addition r' =>
      as_gate_rands_addition r = as_gate_rands_addition r' =>
      get_local_rand pid r = get_local_rand pid r'.
    proof. by case r r' => //; progress; move : H; case r' => //. qed.

    lemma rand_eq_mul r r' pid :
      is_gate_rands_multiplication r => is_gate_rands_multiplication r' =>
      as_gate_rands_multiplication r = as_gate_rands_multiplication r' =>
      get_local_rand pid r = get_local_rand pid r'.
    proof. by case r r' => //; progress; move : H; case r' => //. qed.

    lemma rand_eq_smul r r' pid :
      is_gate_rands_smultiplication r => is_gate_rands_smultiplication r' =>
      as_gate_rands_smultiplication r = as_gate_rands_smultiplication r' =>
      get_local_rand pid r = get_local_rand pid r'.
    proof. by case r r' => //; progress; move : H; case r' => //. qed.

    lemma mul_rgen_ll : islossless BGWMultiplication.R.gen.
    proof.
      proc.
      sp; while (true) (BGWMultiplication.n - i).
        move => z.
        sp; if; first by wp; rnd; skip; smt(dpolynomial_ll n_pos t_pos).
        inline*; wp; rnd; wp; skip; progress; smt(dpolynomial_ll n_pos t_pos).
      by skip => /#. 
    qed.

    lemma inp_rgen_ll : islossless BGWInput.R.gen.
    proof.
      proc.
      sp; while (true) (BGWInput.n - i).
        move => z.
        sp; if; first by wp; rnd; skip; smt(dpolynomial_ll n_pos t_pos).
        inline*; wp; rnd; wp; skip; progress; smt(dpolynomial_ll n_pos t_pos).
      by skip => /#. 
    qed.

    lemma add_rgen_ll : islossless BGWAddition.R.gen.
    proof. by islossless. qed.

    lemma smul_rgen_ll : islossless BGWSMultiplication.R.gen.
    proof. by islossless. qed.

    axiom rp_gen_ll : 
      islossless BGWAddition.R.gen =>
      islossless BGWMultiplication.R.gen =>
      islossless BGWSMultiplication.R.gen =>
      islossless RP(BGWAddition.R, BGWMultiplication.R, BGWSMultiplication.R).gen.

    equiv real_ideal_equiv :
      GameReal(D,R(RP)).main ~ GameIdeal(D,R(RP)).main :
      ={glob D, glob R, glob RP, glob BGWAddition.R, glob BGWMultiplication.R, glob BGWSMultiplication.R,
         c, aux, x} ==> ={res}.
    proof.
proc; inline*.
seq 1 1 : (#pre /\ ={xs,cr}).
by call (_ : true).
sp.
case (valid_corrupted_set cr{2}); last first.
rcondf{1} 4.
progress.
wp.

call (_ : true).
by proc.
proc.
sp.
while (true).
progress.
by skip; progress.
by proc.

skip; progress.
by rewrite H /=.

rcondf{2} 4.
progress.
wp.
call (_ : true).
by proc.
proc.
sp.
while (true).
progress.
by skip; progress.
by proc.

skip; progress.
by rewrite H /=.

rnd. wp. call (_ : true).
by proc.
proc.
sp.
while (0 <= i{2} <= BGWMultiplication.n /\ ={aux,cr,i,ps}).
progress.
sp.
if; first by done.
wp; rnd; skip; progress.
smt().
smt().
inline*.
wp; rnd; wp; skip; progress.
smt().
smt().
skip; progress.
smt(n_pos).
by proc.
by skip; progress.

exists* (cr{2}).
elim* => cr_.
exists* (c{2}).
elim* => c_.

seq 1 1 : (#pre /\ unzip1 grs{1} = unzip1 grs{2} /\ unzip1 grs{1} = range (c_.`1.`1) (c_.`1.`1 + c_.`1.`2 + c_.`1.`4) /\
                      (forall gid, gid \in unzip1 grs{1} => 
                                   (is_gate_rands_input (oget (assoc grs{1} gid)) <=> 
                                    is_gate_rands_input (oget (assoc grs{2} gid))) /\

                                   (is_gate_rands_addition (oget (assoc grs{1} gid)) <=> 
                                    is_gate_rands_addition (oget (assoc grs{2} gid))) /\

                                   (is_gate_rands_multiplication (oget (assoc grs{1} gid)) <=> 
                                    is_gate_rands_multiplication (oget (assoc grs{2} gid))) /\

                                   (is_gate_rands_smultiplication (oget (assoc grs{1} gid)) <=> 
                                    is_gate_rands_smultiplication (oget (assoc grs{2} gid))) /\

                                   (is_gate_rands_input (oget (assoc grs{1} gid)) =>
                                     let rm = as_gate_rands_input (oget (assoc grs{1} gid)) in
                                     let rsm = as_gate_rands_input (oget (assoc grs{2} gid)) in

                                     unzip1 rm = ProtocolFunctionality.pid_set /\ unzip1 rm = unzip1 rsm /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       if pid \in cr_ then get_local_rand pid (oget (assoc grs{1} gid)) =
                                                           get_local_rand pid (oget (assoc grs{2} gid))
                                       else  
                                        (forall x c c', x <> fzero => 
                                          eval x (update (oget (assoc rm pid)) 0 c) = 
                                          eval x (update (oget (assoc rsm pid)) 0 c'))) /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       oget (assoc rm pid) \in dpolynomial ProtocolFunctionality.t) /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       oget (assoc rsm pid) \in dpolynomial ProtocolFunctionality.t)) /\ 

                                   (is_gate_rands_addition (oget (assoc grs{1} gid)) => 
                                     let ra = as_gate_rands_addition (oget (assoc grs{1} gid)) in
                                     let rsa = as_gate_rands_addition (oget (assoc grs{2} gid)) in
                                     ra = rsa /\ BGWAddition.valid_rands ra) /\
 
                                   (is_gate_rands_multiplication (oget (assoc grs{1} gid)) =>
                                     let rm = as_gate_rands_multiplication (oget (assoc grs{1} gid)) in
                                     let rsm = as_gate_rands_multiplication (oget (assoc grs{2} gid)) in

                                     unzip1 rm = ProtocolFunctionality.pid_set /\ unzip1 rm = unzip1 rsm /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       if pid \in cr_ then get_local_rand pid (oget (assoc grs{1} gid)) =
                                                           get_local_rand pid (oget (assoc grs{2} gid))
                                       else  
                                        (forall x c c', x <> fzero => 
                                          eval x (update (oget (assoc rm pid)) 0 c) = 
                                          eval x (update (oget (assoc rsm pid)) 0 c'))) /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       oget (assoc rm pid) \in dpolynomial ProtocolFunctionality.t) /\
                                     (forall pid, pid \in ProtocolFunctionality.pid_set => 
                                       oget (assoc rsm pid) \in dpolynomial ProtocolFunctionality.t)) /\ 

                                    (is_gate_rands_smultiplication (oget (assoc grs{1} gid)) => 
                                      let rsm = as_gate_rands_smultiplication (oget (assoc grs{1} gid)) in
                                      let rssm = as_gate_rands_smultiplication (oget (assoc grs{2} gid)) in
                                      rsm = rssm /\ BGWSMultiplication.valid_rands rsm))).
call (rand_good RP c_ cr_).
skip; progress.
smt().
sp 2 2.
if; last first.
by rnd.
progress.

by rewrite -map_comp /(\o) /= map_id /=.
rewrite !map_assoc //=.
move : H4; rewrite /valid_rands /=.
rewrite -map_comp /(\o) /= map_id /=.
progress.
move : (H7 pid); rewrite H6 /=.
rewrite !map_assoc //=.
rewrite /valid_rand /=.
clear H7.
move : H2 H3.
have : exists (topo, gg), (topo, gg) = c{2} by exists (c{2}).`1 (c{2}).`2 => /#.
move => H7; elim H7 => topo gg /= H7.
rewrite -H7 /=.
have : exists (np, ns, m, q), (np, ns, m, q) = topo by exists topo.`1 topo.`2 topo.`3 topo.`4 => /#.
move => H8; elim H8 => np ns m q /= H8.
rewrite -H8 /=.
progress.
have H10 : topo = c{2}.`1 by smt().
clear H7.
move : H3 H9.

elim gg => //=.

move => gid.
rewrite /valid_inputs => />.
progress.

move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
rewrite !map_assoc //=; first by rewrite mem_range => /#. 
rewrite -get_local_rand_inp.
smt().
rewrite -H26.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) pid).
rewrite H6 /=.
by move : H22; rewrite !map_assoc; first by rewrite mem_range => /#.

have H26 : is_gate_rands_input (oget (assoc grs{1} gid)).
move : H22; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) pid).
smt().
done.

move : H22; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
have ->: is_gate_rands_input (oget (assoc grs{1} gid)).
done.
progress.
move : (H33 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_input (get_local_rand pid (oget (assoc grs{2} gid))) =
oget (assoc (as_gate_rands_input (oget (assoc grs{2} gid))) pid).
rewrite as_local_rand_inp.
move : H25; rewrite !map_assoc //=; first by rewrite mem_range => /#.
done.
progress.
rewrite (dpolynomial_degree _ ProtocolFunctionality.t).
smt(n_pos t_pos).
smt().
done.

have H26 : is_gate_rands_input (oget (assoc grs{1} gid)).
move : H22; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) pid).
smt().
done.

move : H24; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
have ->: is_gate_rands_input (oget (assoc grs{1} gid)).
done.
progress.
move : (H33 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_input (get_local_rand pid (oget (assoc grs{2} gid))) =
oget (assoc (as_gate_rands_input (oget (assoc grs{2} gid))) pid).
rewrite as_local_rand_inp.
move : H25; rewrite !map_assoc //=; first by rewrite mem_range => /#.
done.
progress.
rewrite (dpolynomial_size _ ProtocolFunctionality.t).
smt(n_pos t_pos).
smt().
done.

have H28 : is_gate_rands_input (oget (assoc grs{1} gid)).
move : H22; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) pid).
smt().
done.

move : H24; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
have ->: is_gate_rands_input (oget (assoc grs{1} gid)).
done.
progress.
move : (H34 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_input (get_local_rand pid (oget (assoc grs{2} gid))) =
oget (assoc (as_gate_rands_input (oget (assoc grs{2} gid))) pid).
rewrite as_local_rand_inp.
move : H25; rewrite !map_assoc //=; first by rewrite mem_range => /#.
done.
progress.
rewrite (dpolynomial_exp _ ProtocolFunctionality.t).
smt(n_pos t_pos).
smt().
done.

move => gid wl wr.
rewrite /valid_inputs => />.
progress.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.

rewrite !map_assoc //=; first by rewrite mem_range => /#. 
rewrite -get_local_rand_add.
smt().
rewrite -H37.
rewrite (get_local_rand_add (oget (assoc grs{1} gid)) pid).
rewrite H6 /=.
by move : H32; rewrite !map_assoc; first by rewrite mem_range => /#. 

rewrite H3.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
smt().
split.
smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

rewrite H7.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
smt().
split.
smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

move => gid wl wr.
rewrite /valid_inputs => />.
progress.

move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
rewrite !map_assoc //=; first by rewrite mem_range => /#. 
rewrite -get_local_rand_mul.
smt().
rewrite -H40.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) pid).
rewrite H6 /=.
by move : H32; rewrite !map_assoc; first by rewrite mem_range => /#.

have H38 : is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : H32; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) pid).
smt().
done.

move : H32; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
have ->: is_gate_rands_multiplication (oget (assoc grs{1} gid)).
done.
progress.
move : (H48 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_multiplication (get_local_rand pid (oget (assoc grs{2} gid))) =
oget (assoc (as_gate_rands_multiplication (oget (assoc grs{2} gid))) pid).
rewrite as_local_rand_mul.
move : H33; rewrite !map_assoc //=; first by rewrite mem_range => /#.
done.
progress.
rewrite (dpolynomial_degree _ ProtocolFunctionality.t).
smt(n_pos t_pos).
done.
done.

have H38 : is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : H32; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) pid).
smt().
done.

move : H32; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
have ->: is_gate_rands_multiplication (oget (assoc grs{1} gid)).
done.
progress.
move : (H48 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_multiplication (get_local_rand pid (oget (assoc grs{2} gid))) =
oget (assoc (as_gate_rands_multiplication (oget (assoc grs{2} gid))) pid).
rewrite as_local_rand_mul.
move : H33; rewrite !map_assoc //=; first by rewrite mem_range => /#.
done.
progress.
rewrite (dpolynomial_size _ ProtocolFunctionality.t).
smt(n_pos t_pos).
done.
done.

have H40 : is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : H32; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) pid).
smt().
done.

move : H34; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
have ->: is_gate_rands_multiplication (oget (assoc grs{1} gid)).
done.
progress.
move : (H50 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_multiplication (get_local_rand pid (oget (assoc grs{2} gid))) =
oget (assoc (as_gate_rands_multiplication (oget (assoc grs{2} gid))) pid).
rewrite as_local_rand_mul.
move : H33; rewrite !map_assoc //=; first by rewrite mem_range => /#.
done.
progress.
rewrite (dpolynomial_exp _ ProtocolFunctionality.t).
smt(n_pos t_pos).
done.
done.

rewrite H3.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
smt().
split.
smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

rewrite H7.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
smt().
split.
smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

move => gid wl wr.
rewrite /valid_inputs => />.
progress.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.

rewrite !map_assoc //=; first by rewrite mem_range => /#. 
rewrite -get_local_rand_smul.
smt().
rewrite -H39.
rewrite (get_local_rand_smul (oget (assoc grs{1} gid)) pid).
rewrite H6 /=.
by move : H32; rewrite !map_assoc; first by rewrite mem_range => /#. 

rewrite H3.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
split.
smt().
split.
smt().
split.
move : H19 H23.
clear H34 H17 H15 H3.
by case wl => //=.
smt().
split.

smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

rewrite H7.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
split.
smt().
split.
smt().
split.
move : H19 H23.
clear H34 H17 H15 H3.
by case wl => //=.
smt().
split.
smt().
split.
smt().
rewrite /valid_inputs_topology /=.
progress.
smt().


by rewrite -map_comp /(\o) /= map_id /=.
rewrite !map_assoc //=.
move : H4; rewrite /valid_rands /=.
rewrite -map_comp /(\o) /= map_id /=.
progress.
move : (H7 pid); rewrite H6 /=.
rewrite !map_assoc //=.
rewrite /valid_rand /=.
clear H7.
move : H2 H3.
have : exists (topo, gg), (topo, gg) = c{2} by exists (c{2}).`1 (c{2}).`2 => /#.
move => H7; elim H7 => topo gg /= H7.
rewrite -H7 /=.
have : exists (np, ns, m, q), (np, ns, m, q) = topo by exists topo.`1 topo.`2 topo.`3 topo.`4 => /#.
move => H8; elim H8 => np ns m q /= H8.
rewrite -H8 /=.
progress.
have H10 : topo = c{2}.`1 by smt().
clear H7.
move : H3 H9.

elim gg => //=.

move => gid.
rewrite /valid_inputs => />.
progress.

move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
rewrite !map_assoc //=; first by rewrite mem_range => /#. 
rewrite -get_local_rand_inp.
smt().
rewrite H26.
rewrite (get_local_rand_inp (oget (assoc grs{2} gid)) pid).
rewrite H6 /=.
by move : H22; rewrite !map_assoc; first by rewrite mem_range => /#.

(****)
have H26 : is_gate_rands_input (oget (assoc grs{1} gid)).
move : H22; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) pid).
smt().
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
smt().
(****)

move : H24; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
have ->: is_gate_rands_input (oget (assoc grs{1} gid)).
done.
progress.
move : (H33 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_input (get_local_rand pid (oget (assoc grs{1} gid))) =
oget (assoc (as_gate_rands_input (oget (assoc grs{1} gid))) pid).
rewrite as_local_rand_inp.
move : H25; rewrite !map_assoc //=; first by rewrite mem_range => /#.
done.
progress.
rewrite (dpolynomial_degree _ ProtocolFunctionality.t).
smt(n_pos t_pos).
smt().
done.

(****)
have H26 : is_gate_rands_input (oget (assoc grs{1} gid)).
move : H22; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) pid).
smt().
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
smt().
(****)

move : H24; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
have ->: is_gate_rands_input (oget (assoc grs{1} gid)).
done.
progress.
move : (H33 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_input (get_local_rand pid (oget (assoc grs{1} gid))) =
oget (assoc (as_gate_rands_input (oget (assoc grs{1} gid))) pid).
rewrite as_local_rand_inp.
move : H25; rewrite !map_assoc //=; first by rewrite mem_range => /#.
done.
progress.
rewrite (dpolynomial_size _ ProtocolFunctionality.t).
smt(n_pos t_pos).
smt().
done.

(****)
have H28 : is_gate_rands_input (oget (assoc grs{1} gid)).
move : H22; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) pid).
smt().
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
smt().
(****)

move : H25; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
have ->: is_gate_rands_input (oget (assoc grs{1} gid)).
done.
progress.
move : (H35 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_input (get_local_rand pid (oget (assoc grs{1} gid))) =
oget (assoc (as_gate_rands_input (oget (assoc grs{1} gid))) pid).
rewrite as_local_rand_inp.
move : H22; rewrite !map_assoc //=; first by rewrite mem_range => /#.
done.
progress.
rewrite (dpolynomial_exp _ ProtocolFunctionality.t).
smt(n_pos t_pos).
smt().
done.

move => gid wl wr.
rewrite /valid_inputs => />.
progress.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.

rewrite !map_assoc //=; first by rewrite mem_range => /#. 
rewrite -get_local_rand_add.
smt().
rewrite H37.
rewrite (get_local_rand_add (oget (assoc grs{2} gid)) pid).
rewrite H6 /=.
by move : H32; rewrite !map_assoc; first by rewrite mem_range => /#. 

rewrite H3.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
smt().
split.
smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

rewrite H7.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
smt().
split.
smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

move => gid wl wr.
rewrite /valid_inputs => />.
progress.

move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
rewrite !map_assoc //=; first by rewrite mem_range => /#. 
rewrite -get_local_rand_mul.
smt().
rewrite H40.
rewrite (get_local_rand_mul (oget (assoc grs{2} gid)) pid).
rewrite H6 /=.
by move : H32; rewrite !map_assoc; first by rewrite mem_range => /#.

(****)
have H38 : is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : H32; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) pid).
smt().
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
smt.
(****)

move : H32; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
move : H44.
have ->: is_gate_rands_multiplication (oget (assoc grs{1} gid)).
done.
progress.
move : (H49 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_multiplication (get_local_rand pid (oget (assoc grs{1} gid))) =
oget (assoc (as_gate_rands_multiplication (oget (assoc grs{1} gid))) pid).
rewrite as_local_rand_mul.
smt().
done.
progress.
rewrite (dpolynomial_degree _ ProtocolFunctionality.t).
smt(n_pos t_pos).
done.
done.

(****)
have H38 : is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : H32; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) pid).
smt().
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
smt.
(****)

move : H32; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
move : H44.
have ->: is_gate_rands_multiplication (oget (assoc grs{1} gid)).
done.
progress.
move : (H49 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_multiplication (get_local_rand pid (oget (assoc grs{1} gid))) =
oget (assoc (as_gate_rands_multiplication (oget (assoc grs{1} gid))) pid).
rewrite as_local_rand_mul.
smt().
done.
progress.
rewrite (dpolynomial_size _ ProtocolFunctionality.t).
smt(n_pos t_pos).
done.
done.

(****)
have H40 : is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : H32; rewrite !map_assoc //=; first by rewrite mem_range => /#.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) pid).
smt().
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
smt.
(****)

move : H34; rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.
move : H46.
have ->: is_gate_rands_multiplication (oget (assoc grs{1} gid)).
done.
progress.
move : (H51 pid); rewrite H6 /=.
rewrite /get_local_rand.
have ->: as_gate_rand_multiplication (get_local_rand pid (oget (assoc grs{1} gid))) =
oget (assoc (as_gate_rands_multiplication (oget (assoc grs{1} gid))) pid).
rewrite as_local_rand_mul.
smt().
done.
progress.
rewrite (dpolynomial_exp _ ProtocolFunctionality.t).
smt(n_pos t_pos).
done.
done.

rewrite H3.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
smt().
split.
smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

rewrite H7.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
smt().
split.
smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

(**** SMULTIPLICATION ****)

move => gid wl wr.
rewrite /valid_inputs => />.
progress.
move : (H2 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H1.
rewrite mem_range .
simplify.
smt().
progress.

rewrite !map_assoc //=; first by rewrite mem_range => /#. 
rewrite -get_local_rand_smul.
smt().
rewrite H39.
rewrite (get_local_rand_smul (oget (assoc grs{2} gid)) pid).
rewrite H6 /=.
by move : H32; rewrite !map_assoc; first by rewrite mem_range => /#. 

rewrite H3.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
split.
smt().
split.
smt().
split.
move : H19 H23.
clear H34 H17 H15 H3.
by case wl => //=.
smt().
split.

smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

rewrite H7.
split.
rewrite /valid_circuit /=.
have ->: valid_topology (np, ns, m, q).
rewrite /valid_topology /=.
smt().
rewrite /valid_gates /=.
split.
smt().
split.
smt().
split.
move : H19 H23.
clear H34 H17 H15 H3.
by case wl => //=.
smt().
split.
smt().
split.
smt().
rewrite /valid_inputs_topology /=.
progress.
smt().

call (_ : true).
wp; skip. 
move => /> &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8. 

(************* SIMULATOR ****************)

rewrite /simulator /=.
move : H2 H4 H6 H7 H8; elim (c_) => topo gg /=.
elim topo => np ns m q /=.
rewrite /valid_inputs /valid_rands /=.
rewrite /valid_circuit /=.
rewrite /valid_inputs_topology /=.
rewrite /valid_topology /valid_gates /=.
rewrite /valid_secret /=.
rewrite /valid_rand /=.
rewrite -map_comp /(\o) /= map_id /=.
move => /> H2 H4 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18. 
rewrite /protocol /= /eval_circuit /= /trace /=.
move : H10 H11 H12 H13 H18.
elim gg => //=.

move => /> w H19 H20; progress
rewrite /pinput /sinput /input /= /rand.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first 3 by smt().
rewrite !map_assoc //=; first by smt().
move : (H16 w); rewrite H19 H20 /=.
progress.
move : H11; rewrite allP; progress.
have : (head witness HMShamir.SecretSharingScheme.pid_set, nth witness (oget (assoc xs{2} (head witness HMShamir.SecretSharingScheme.pid_set))).`1 w) \in map
         (fun (pid : SecretSharingScheme.pid_t) =>
            (pid, nth witness ((pinput pid xs{2}))%ArithmeticProtocolFunctionality w)) SecretSharingScheme.pid_set.
rewrite mapP; progress.
exists (head witness HMShamir.SecretSharingScheme.pid_set).
have ->: head witness HMShamir.SecretSharingScheme.pid_set \in SecretSharingScheme.pid_set.
smt(n_pos pid_set_size).
by rewrite /pinput /input /=.
have : (head witness cr_, nth witness (oget (assoc xs{2} (head witness cr_))).`1 w) \in map
         (fun (pid : SecretSharingScheme.pid_t) =>
            (pid, nth witness ((pinput pid xs{2}))%ArithmeticProtocolFunctionality w)) SecretSharingScheme.pid_set.
rewrite mapP; progress.
exists (head witness cr_).
have ->: head witness cr_ \in SecretSharingScheme.pid_set.
smt(n_pos pid_set_size).
by rewrite /pinput /input /=.
progress.
smt().

(***)
rewrite /pinput /sinput /input /= /rand.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.
rewrite !map_assoc //=; first 2 by smt().
rewrite -eq_in_map => gid; progress.
move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
by rewrite H2 //=. 
progress.
case (is_gate_rands_addition (oget (assoc grs{1} gid))); progress.
rewrite (rand_eq_add (oget (assoc grs{1} gid)) (oget (assoc grs{2} gid))).
done.
smt().
smt().
done.
case (is_gate_rands_multiplication (oget (assoc grs{1} gid))); progress.
move : H24; rewrite H27 /=; progress.
move : (H29 x0).
have ->: x0 \in ProtocolFunctionality.pid_set by smt().
rewrite H10 /=.
done.
case (is_gate_rands_smultiplication (oget (assoc grs{1} gid))); progress.
rewrite (rand_eq_smul (oget (assoc grs{1} gid)) (oget (assoc grs{2} gid))).
done.
smt().
smt().
done.
smt().
rewrite !map_assoc //=; first 2 by smt().
rewrite !map_assoc //=; first by smt().
rewrite /input /=.
move : (H16 w); rewrite H19 H20 /=.
progress.
move : H11; rewrite allP; progress.
have : (head witness HMShamir.SecretSharingScheme.pid_set, nth witness (oget (assoc xs{2} (head witness HMShamir.SecretSharingScheme.pid_set))).`1 w) \in map
         (fun (pid : SecretSharingScheme.pid_t) =>
            (pid, nth witness ((pinput pid xs{2}))%ArithmeticProtocolFunctionality w)) SecretSharingScheme.pid_set.
rewrite mapP; progress.
exists (head witness HMShamir.SecretSharingScheme.pid_set).
have ->: head witness HMShamir.SecretSharingScheme.pid_set \in SecretSharingScheme.pid_set.
smt(n_pos pid_set_size).
by rewrite /pinput /input /=.
have : (head witness cr_, nth witness (oget (assoc xs{2} (head witness cr_))).`1 w) \in map
         (fun (pid : SecretSharingScheme.pid_t) =>
            (pid, nth witness ((pinput pid xs{2}))%ArithmeticProtocolFunctionality w)) SecretSharingScheme.pid_set.
rewrite mapP; progress.
exists (head witness cr_).
have ->: head witness cr_ \in SecretSharingScheme.pid_set.
smt(n_pos pid_set_size).
by rewrite /pinput /input /=.
progress.
smt().
(***)


move => /> gid H18 H19 H20.

(*** outputs ***)
progress.
rewrite /simulator /=.
pose rss := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{2} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
pose rs := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{1} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).

rewrite /eval /= /party_exec1 /party_exec2 /=.
rewrite /input /=.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first 2 by smt().
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
rewrite /output /=.
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
rewrite -!map_comp /(\o) /=.
rewrite /get_messages_to /=.
congr.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.
case (x1 \in cr_); progress.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
by rewrite mem_range => /#.
by rewrite mem_range => /#.

rewrite /sinput /input /extract_inputs /=.
rewrite !map_assoc //=.
rewrite /input /=.
move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
by rewrite H2 mem_range => /#.
simplify.

have ->: as_gate_rand_input (get_local_rand x1 (oget (assoc grs{1} gid))) = as_gate_rand_input (get_local_rand x1 (oget (assoc grs{2} gid))).
move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H2 mem_range => /#.
progress.
move : H24.
have ->: is_gate_rands_input (oget (assoc grs{1} gid)).
move : (H20 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) x1).
smt().
done.
progress.
smt().
done.

move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H2 mem_range => /#.
progress.
move : H24.
have ->: is_gate_rands_input (oget (assoc grs{1} gid)).
move : (H20 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) x1).
smt().
done.
progress.
move : (H29 x1); rewrite H12 /=.
have ->: x1 \in ProtocolFunctionality.pid_set by smt().
progress.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
rewrite /share /=.
rewrite !map_assoc //=; first 2 by smt().
rewrite -as_local_rand_inp.
move : (H20 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) x1).
smt().
done.
have : is_gate_rands_input (oget (assoc grs{1} gid)).
move : (H20 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) x1).
smt().
done.
progress.
rewrite -as_local_rand_inp.
move : (H20 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_inp (oget (assoc grs{2} gid)) x1).
smt().
smt().
rewrite /sinput /input /=.
rewrite (H32 x0 (nth witness (oget (assoc xs{2} x1)).`2 gid) (fzero)).
rewrite pid_set_neq0.
smt().
done.
done.

(***)
rewrite /simulator /=.
pose rss := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{2} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
pose rs := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{1} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
rewrite /eval /= /party_exec1 /party_exec2 /=.
rewrite /input /=.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.
rewrite /rs /rss /rand.
rewrite !map_assoc //=; first 2 by smt().
rewrite -eq_in_map => gid'; progress.
move : (H3 gid').
have ->: gid' \in unzip1 grs{1}.
by rewrite H2 //=. 
progress.
case (is_gate_rands_addition (oget (assoc grs{1} gid'))); progress.
rewrite (rand_eq_add (oget (assoc grs{1} gid')) (oget (assoc grs{2} gid'))).
done.
smt().
smt().
done.
case (is_gate_rands_multiplication (oget (assoc grs{1} gid'))); progress.
move : H25; rewrite H28 /=; progress.
move : (H30 x0).
have ->: x0 \in ProtocolFunctionality.pid_set by smt().
rewrite H10 /=.
done.
case (is_gate_rands_smultiplication (oget (assoc grs{1} gid'))); progress.
rewrite (rand_eq_smul (oget (assoc grs{1} gid')) (oget (assoc grs{2} gid'))).
done.
smt().
smt().
done.
smt().
rewrite !map_assoc //=; first 2 by smt().
rewrite !map_assoc //=; first 2 by smt().

rewrite !map_assoc //=; first by smt().
rewrite -!map_comp /(\o) /=.
rewrite -eq_in_map; progress.
rewrite /get_messages_to /=.
rewrite !map_assoc //=.
case (x1 \in cr_); progress.
rewrite !map_assoc //=.
rewrite /share /=.
rewrite !map_assoc //=; first by smt().
by rewrite mem_range => /#.
smt().
by rewrite mem_range => /#.

move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H2 mem_range => /#.
progress.
move : H24.
have ->: is_gate_rands_input (oget (assoc grs{1} gid)).
move : (H20 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_inp (oget (assoc grs{1} gid)) x1).
smt().
done.
progress.
move : (H29 x1); rewrite H11 H12 /=. 
progress.
rewrite H32 /sinput /input /extract_inputs /=.
by rewrite !map_assoc //=.

move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H2 mem_range => /#.
progress.
move : H24.
have ->: is_gate_rands_input (oget (assoc grs{1} gid)).
move : (H20 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
smt().
progress.
move : (H29 x1); rewrite H11 H12 /=. 
progress.
rewrite !map_assoc //= /share /= /eval !map_assoc //=.
smt(). rewrite mem_range => /#. smt(). rewrite mem_range => /#.
rewrite /sinput /input /=.
have ->: as_gate_rand_input (get_local_rand x1 (oget (assoc grs{1} gid))) = 
         oget (assoc (as_gate_rands_input (oget (assoc grs{1} gid))) x1).
rewrite as_local_rand_inp.
move : (H20 x1). 
rewrite H11 /=.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
smt().
done.
rewrite (H32 x0 (nth witness (oget (assoc xs{2} x1)).`2 gid) (fzero)).
smt.
rewrite as_local_rand_inp.
move : (H20 x1). 
rewrite H11 /=.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
smt().
done.

(***)

(*move => w; progress.
rewrite /pinput /sinput /input /= /rand.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().
(***)
rewrite /pinput /sinput /input /= /rand.
rewrite -eq_in_map; progress.
rewrite /extract_inputs.
by rewrite !map_assoc //=. 
rewrite !map_assoc //=; first 2 by smt().
rewrite -eq_in_map => gid; progress.
move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
by rewrite H2 //=. 
progress.
case (is_gate_rands_addition (oget (assoc grs{1} gid))); progress.
rewrite (rand_eq_add (oget (assoc grs{1} gid)) (oget (assoc grs{2} gid))).
done.
smt().
smt().
done.
case (is_gate_rands_multiplication (oget (assoc grs{1} gid))); progress.
move : H23; rewrite H26 /=; progress.
move : (H28 x0).
have ->: x0 \in ProtocolFunctionality.pid_set by smt().
rewrite H11 /=.
done.
case (is_gate_rands_smultiplication (oget (assoc grs{1} gid))); progress.
rewrite (rand_eq_smul (oget (assoc grs{1} gid)) (oget (assoc grs{2} gid))).
done.
smt().
smt().
done.
smt().
rewrite !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().
(***)*)

move => gid c; progress.
rewrite /pinput /sinput /input /= /rand.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first 2 by smt().
by rewrite !map_assoc //=; first by smt().
(***)
rewrite /pinput /sinput /input /= /rand.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=. 
rewrite !map_assoc //=; first 2 by smt().
rewrite -eq_in_map => gid'; progress.
move : (H3 gid').
have ->: gid' \in unzip1 grs{1}.
by rewrite H2 //=. 
progress.
case (is_gate_rands_addition (oget (assoc grs{1} gid'))); progress.
rewrite (rand_eq_add (oget (assoc grs{1} gid')) (oget (assoc grs{2} gid'))).
done.
smt().
smt().
done.
case (is_gate_rands_multiplication (oget (assoc grs{1} gid'))); progress.
move : H23; rewrite H26 /=; progress.
move : (H28 x0).
have ->: x0 \in ProtocolFunctionality.pid_set by smt().
rewrite H11 /=.
done.
case (is_gate_rands_smultiplication (oget (assoc grs{1} gid'))); progress.
rewrite (rand_eq_smul (oget (assoc grs{1} gid')) (oget (assoc grs{2} gid'))).
done.
smt().
smt().
done.
smt().
rewrite !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().
(***)

(*********  ADDITION SIMULATION *****************)

move => /> gid wl wr H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31.
move : H19.
have ->: valid_input_gates np ns wl by smt().
have ->: valid_constant_gates np ns wl by smt().
have ->: valid_smultiplication_gates wl by smt().
have ->: valid_gids np ns q wl by smt().
have ->: (forall (pid : pid_t),
    pid \in ArithP.ProtocolFunctionality.pid_set =>
    gates_valid_rand wl
      (oget
         (assoc
            (map
               (fun (pid0 : pid_t) =>
                  (pid0,
                   map (fun (gid0 : gid_t) => (gid0, get_local_rand pid0 (oget (assoc grs{1} gid0))))
                     (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set) pid))) <=> true.
progress.
move : (H31 pid); rewrite H10 /=.
by done.
simplify => /> Hsim1l Hsim2l.
move : H20.
have ->: valid_input_gates np ns wr by smt().
have ->: valid_constant_gates np ns wr by smt().
have ->: valid_smultiplication_gates wr by smt().
have ->: valid_gids np ns q wr by smt().
have ->: (forall (pid : pid_t),
    pid \in ArithP.ProtocolFunctionality.pid_set =>
    gates_valid_rand wr
      (oget
         (assoc
            (map
               (fun (pid0 : pid_t) =>
                  (pid0,
                   map (fun (gid0 : gid_t) => (gid0, get_local_rand pid0 (oget (assoc grs{1} gid0))))
                     (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set) pid))) <=> true.
progress.
move : (H31 pid); rewrite H10 /=.
by done.
simplify => /> Hsim1r Hsim2r.

(*** outputs ***)
progress.
rewrite /simulator /=.
move : Hsim1l Hsim2l Hsim1r Hsim2r H31.
pose rss := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{2} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
pose rs := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{1} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
move => Hsim1l Hsim2l Hsim1r Hsim2r H31.
have gates_l : exists (tl, vwl), (tl, vwl) = eval_gates wl rs xs{2}.
exists (eval_gates wl rs xs{2}).`1 (eval_gates wl rs xs{2}).`2 => /#.
elim gates_l => tl vwl gates_l /=; rewrite -gates_l /=.
have gates_r : exists (tr, vwr), (tr, vwr) = eval_gates wr rs xs{2}.
exists (eval_gates wr rs xs{2}).`1 (eval_gates wr rs xs{2}).`2 => /#.
elim gates_r => tr vwr gates_r /=; rewrite -gates_r /=.
have sgates_l : exists (vwls, tls), (vwls, tls) = simulate_gates wl rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_l => vwls tls sgates_l /=; rewrite -sgates_l /=.
have sgates_r : exists (vwrs, trs), (vwrs, trs) = simulate_gates wr rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_r => vwrs trs sgates_r /=; rewrite -sgates_r /=.
rewrite /eval /= /party_exec /=.
rewrite /input /=.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
have ->: (oget (assoc vwl x0)) = (oget (assoc vwls x0)).
have ->: vwls = (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`1.
smt().
rewrite -Hsim1l.
rewrite !map_assoc //=.
rewrite -gates_l /=.
rewrite !map_assoc //=; first by smt().
have ->: (oget (assoc vwr x0)) = (oget (assoc vwrs x0)).
have ->: vwrs = (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`1.
smt().
rewrite -Hsim1r.
rewrite !map_assoc //=.
rewrite -gates_r /=.
rewrite !map_assoc //=; first by smt().
done.

(***)
rewrite /simulator /=.

move : Hsim1l Hsim2l Hsim1r Hsim2r H31.
pose rss := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{2} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
pose rs := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{1} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
move => Hsim1l Hsim2l Hsim1r Hsim2r H31.
have gates_l : exists (tl, vwl), (tl, vwl) = eval_gates wl rs xs{2}.
exists (eval_gates wl rs xs{2}).`1 (eval_gates wl rs xs{2}).`2 => /#.
elim gates_l => tl vwl gates_l /=; rewrite -gates_l /=.
have gates_r : exists (tr, vwr), (tr, vwr) = eval_gates wr rs xs{2}.
exists (eval_gates wr rs xs{2}).`1 (eval_gates wr rs xs{2}).`2 => /#.
elim gates_r => tr vwr gates_r /=; rewrite -gates_r /=.
have sgates_l : exists (vwls, tls), (vwls, tls) = simulate_gates wl rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_l => vwls tls sgates_l /=; rewrite -sgates_l /=.
have sgates_r : exists (vwrs, trs), (vwrs, trs) = simulate_gates wr rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_r => vwrs trs sgates_r /=; rewrite -sgates_r /=.
rewrite /eval /= /party_exec /=.
rewrite /input /=.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=. 
rewrite /rs /rss /rand.
rewrite !map_assoc //=; first 2 by smt().
rewrite -eq_in_map => gid'; progress.
move : (H3 gid').
have ->: gid' \in unzip1 grs{1}.
by rewrite H2 //=. 
progress.
case (is_gate_rands_addition (oget (assoc grs{1} gid'))); progress.
rewrite (rand_eq_add (oget (assoc grs{1} gid')) (oget (assoc grs{2} gid'))).
done.
smt().
smt().
done.
case (is_gate_rands_multiplication (oget (assoc grs{1} gid'))); progress.
move : H33; rewrite H36 /=; progress.
move : (H38 x0).
have ->: x0 \in ProtocolFunctionality.pid_set by smt().
rewrite H10 /=.
done.
case (is_gate_rands_smultiplication (oget (assoc grs{1} gid'))); progress.
rewrite (rand_eq_smul (oget (assoc grs{1} gid')) (oget (assoc grs{2} gid'))).
done.
smt().
smt().
done.
smt().
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
split.
by rewrite !map_assoc //=; first by smt().
split.
have ->: tls = (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`2 by smt().
rewrite -Hsim2l.
rewrite !map_assoc //=.
rewrite -gates_l /=.
rewrite !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().
have ->: trs = (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`2 by smt().
rewrite -Hsim2r.
rewrite !map_assoc //=.
rewrite -gates_r /=.
rewrite !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().
(***)

(*********  MULTIPLICATION SIMULATION *****************)

move => /> gid wl wr H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31.
move : H19.
have ->: valid_input_gates np ns wl by smt().
have ->: valid_constant_gates np ns wl by smt().
have ->: valid_smultiplication_gates wl by smt().
have ->: valid_gids np ns q wl by smt().
have ->: (forall (pid : pid_t),
    pid \in ArithP.ProtocolFunctionality.pid_set =>
    gates_valid_rand wl
      (oget
         (assoc
            (map
               (fun (pid0 : pid_t) =>
                  (pid0,
                   map (fun (gid0 : gid_t) => (gid0, get_local_rand pid0 (oget (assoc grs{1} gid0))))
                     (range (np ) (np + ns + q)))) ProtocolFunctionality.pid_set) pid))) <=> true.
progress.
move : (H31 pid); rewrite H10 /=.
by done.
simplify => /> Hsim1l Hsim2l.
move : H20.
have ->: valid_input_gates np ns wr by smt().
have ->: valid_constant_gates np ns wr by smt().
have ->: valid_smultiplication_gates wr by smt().
have ->: valid_gids np ns q wr by smt().
have ->: (forall (pid : pid_t),
    pid \in ArithP.ProtocolFunctionality.pid_set =>
    gates_valid_rand wr
      (oget
         (assoc
            (map
               (fun (pid0 : pid_t) =>
                  (pid0,
                   map (fun (gid0 : gid_t) => (gid0, get_local_rand pid0 (oget (assoc grs{1} gid0))))
                     (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set) pid))) <=> true.
progress.
move : (H31 pid); rewrite H10 /=.
by done.
simplify => /> Hsim1r Hsim2r.

(*** outputs ***)
progress.
rewrite /simulator /=.
move : Hsim1l Hsim2l Hsim1r Hsim2r H31.
pose rss := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{2} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
pose rs := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{1} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
move => Hsim1l Hsim2l Hsim1r Hsim2r H31.
have gates_l : exists (tl, vwl), (tl, vwl) = eval_gates wl rs xs{2}.
exists (eval_gates wl rs xs{2}).`1 (eval_gates wl rs xs{2}).`2 => /#.
elim gates_l => tl vwl gates_l /=; rewrite -gates_l /=.
have gates_r : exists (tr, vwr), (tr, vwr) = eval_gates wr rs xs{2}.
exists (eval_gates wr rs xs{2}).`1 (eval_gates wr rs xs{2}).`2 => /#.
elim gates_r => tr vwr gates_r /=; rewrite -gates_r /=.
have sgates_l : exists (vwls, tls), (vwls, tls) = simulate_gates wl rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_l => vwls tls sgates_l /=; rewrite -sgates_l /=.
have sgates_r : exists (vwrs, trs), (vwrs, trs) = simulate_gates wr rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_r => vwrs trs sgates_r /=; rewrite -sgates_r /=.
rewrite /eval /= /party_exec1 /party_exec2 /=.
rewrite /input /=.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first 2 by smt().
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
rewrite /output /=.
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
rewrite -!map_comp /(\o) /=.
rewrite /get_messages_to /=.
congr.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.
case (x1 \in cr_); progress.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
by rewrite mem_range => /#.
by rewrite mem_range => /#.

have ->: (oget (assoc vwl x1)) = (oget (assoc vwls x1)).
have ->: vwls = (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`1.
smt().
rewrite -Hsim1l.
rewrite !map_assoc //=.
rewrite -gates_l /=.
by rewrite !map_assoc //=.
have ->: (oget (assoc vwr x1)) = (oget (assoc vwrs x1)).
have ->: vwrs = (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`1.
smt().
rewrite -Hsim1r.
rewrite !map_assoc //=.
rewrite -gates_r /=.
by rewrite !map_assoc //=.
have ->: as_gate_rand_multiplication (get_local_rand x1 (oget (assoc grs{1} gid))) = as_gate_rand_multiplication (get_local_rand x1 (oget (assoc grs{2} gid))).
move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H2 mem_range => /#.
progress.
move : H34.
have ->: is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : (H31 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) x1).
smt().
done.
progress.
smt().
done.

move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H2 mem_range => /#.
progress.
move : H34.
have ->: is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : (H31 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) x1).
smt().
done.
progress.
move : (H37 x1); rewrite H12 /=.
have ->: x1 \in ProtocolFunctionality.pid_set by smt().
progress.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
rewrite /share /=.
rewrite !map_assoc //=; first 2 by smt().
rewrite -as_local_rand_mul.
move : (H31 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) x1).
smt().
done.
have : is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : (H31 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) x1).
smt().
done.
progress.
rewrite -as_local_rand_mul.
move : (H31 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_mul (oget (assoc grs{2} gid)) x1).
smt().
smt().
rewrite (H40 x0 (fmul (oget (assoc vwl x1)) (oget (assoc vwr x1))) (fmul fzero fzero)).
rewrite pid_set_neq0.
smt().
done.
done.

(***)
rewrite /simulator /=.
move : Hsim1l Hsim2l Hsim1r Hsim2r H31.
pose rss := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{2} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
pose rs := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{1} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
move => Hsim1l Hsim2l Hsim1r Hsim2r H31.
have gates_l : exists (tl, vwl), (tl, vwl) = eval_gates wl rs xs{2}.
exists (eval_gates wl rs xs{2}).`1 (eval_gates wl rs xs{2}).`2 => /#.
elim gates_l => tl vwl gates_l /=; rewrite -gates_l /=.
have gates_r : exists (tr, vwr), (tr, vwr) = eval_gates wr rs xs{2}.
exists (eval_gates wr rs xs{2}).`1 (eval_gates wr rs xs{2}).`2 => /#.
elim gates_r => tr vwr gates_r /=; rewrite -gates_r /=.
have sgates_l : exists (vwls, tls), (vwls, tls) = simulate_gates wl rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_l => vwls tls sgates_l /=; rewrite -sgates_l /=.
have sgates_r : exists (vwrs, trs), (vwrs, trs) = simulate_gates wr rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_r => vwrs trs sgates_r /=; rewrite -sgates_r /=.
rewrite /eval /= /party_exec1 /party_exec2 /=.
rewrite /input /=.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.
rewrite /rs /rss /rand.
rewrite !map_assoc //=; first 2 by smt().
rewrite -eq_in_map => gid'; progress.
move : (H3 gid').
have ->: gid' \in unzip1 grs{1}.
by rewrite H2 //=. 
progress.
case (is_gate_rands_addition (oget (assoc grs{1} gid'))); progress.
rewrite (rand_eq_add (oget (assoc grs{1} gid')) (oget (assoc grs{2} gid'))).
done.
smt().
smt().
done.
case (is_gate_rands_multiplication (oget (assoc grs{1} gid'))); progress.
move : H33; rewrite H36 /=; progress.
move : (H38 x0).
have ->: x0 \in ProtocolFunctionality.pid_set by smt().
rewrite H10 /=.
done.
case (is_gate_rands_smultiplication (oget (assoc grs{1} gid'))); progress.
rewrite (rand_eq_smul (oget (assoc grs{1} gid')) (oget (assoc grs{2} gid'))).
done.
smt().
smt().
done.
smt().
rewrite !map_assoc //=; first 2 by smt().
rewrite !map_assoc //=; first 2 by smt().
split.

rewrite !map_assoc //=; first by smt().
rewrite -!map_comp /(\o) /=.
rewrite -eq_in_map; progress.
rewrite /get_messages_to /=.
rewrite !map_assoc //=.
case (x1 \in cr_); progress.
rewrite !map_assoc //=.
rewrite /share /=.
rewrite !map_assoc //=; first by smt().
by rewrite mem_range => /#.
smt().
by rewrite mem_range => /#.

move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H2 mem_range => /#.
progress.
move : H34.
have ->: is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : (H31 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) x1).
smt().
done.
progress.
move : (H37 x1); rewrite H11 H12 /=. 
progress.
rewrite H40.
have ->: (oget (assoc vwl x1)) = (oget (assoc vwls x1)).
have ->: vwls = (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`1.
smt().
rewrite -Hsim1l.
rewrite !map_assoc //=.
rewrite -gates_l /=.
by rewrite !map_assoc //=.
have ->: (oget (assoc vwr x1)) = (oget (assoc vwrs x1)).
have ->: vwrs = (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`1.
smt().
rewrite -Hsim1r.
rewrite !map_assoc //=.
rewrite -gates_r /=.
by rewrite !map_assoc //=.
done.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first 2 by rewrite mem_range => /#.
rewrite /share /=.
rewrite !map_assoc //=; first 2 by smt().
rewrite -as_local_rand_mul.
move : (H31 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) x1).
smt().
done.
have : is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : (H31 x1); rewrite H11 /=.
rewrite /rs.
rewrite !map_assoc //=.
rewrite !map_assoc //=; first by rewrite mem_range => /#.
progress.
rewrite (get_local_rand_mul (oget (assoc grs{1} gid)) x1).
smt().
done.

move : (H3 gid).
have ->: gid \in unzip1 grs{1}.
rewrite H2 mem_range => /#.
progress.
move : H34.
have ->: is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : (H31 x1); rewrite H11 /=.
rewrite /rs.
by rewrite !map_assoc //=.
progress.
move : (H38 x1); rewrite H11 H12 /=. 
progress.
rewrite (H41 x0 (fmul (oget (assoc vwl x1)) (oget (assoc vwr x1))) (fmul fzero fzero)).
smt.
have : is_gate_rands_multiplication (oget (assoc grs{1} gid)).
move : (H31 x1); rewrite H11 /=.
rewrite /rs.
by rewrite !map_assoc //=.
progress.
rewrite as_local_rand_mul.
smt().
done.

split.
have ->: tls = (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`2 by smt().
rewrite -Hsim2l.
rewrite !map_assoc //=.
rewrite -gates_l /=.
rewrite !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().
have ->: trs = (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`2 by smt().
rewrite -Hsim2r.
rewrite !map_assoc //=.
rewrite -gates_r /=.
rewrite !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().
(***)

(*********  SMULTIPLICATION SIMULATION *****************)

move => /> gid wl wr H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31.
move : H19.
have ->: valid_input_gates np ns wl by smt().
have ->: valid_constant_gates np ns wl by smt().
have ->: valid_smultiplication_gates wl by smt().
have ->: valid_gids np ns q wl by smt().
have ->: (forall (pid : pid_t),
    pid \in ArithP.ProtocolFunctionality.pid_set =>
    gates_valid_rand wl
      (oget
         (assoc
            (map
               (fun (pid0 : pid_t) =>
                  (pid0,
                   map (fun (gid0 : gid_t) => (gid0, get_local_rand pid0 (oget (assoc grs{1} gid0))))
                     (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set) pid))) <=> true.
progress.
move : (H31 pid); rewrite H10 /=.
by done.
simplify => /> Hsim1l Hsim2l.
move : H20.
have ->: valid_input_gates np ns wr by smt().
have ->: valid_constant_gates np ns wr by smt().
have ->: valid_smultiplication_gates wr by smt().
have ->: valid_gids np ns q wr by smt().
have ->: (forall (pid : pid_t),
    pid \in ArithP.ProtocolFunctionality.pid_set =>
    gates_valid_rand wr
      (oget
         (assoc
            (map
               (fun (pid0 : pid_t) =>
                  (pid0,
                   map (fun (gid0 : gid_t) => (gid0, get_local_rand pid0 (oget (assoc grs{1} gid0))))
                     (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set) pid))) <=> true.
progress.
move : (H31 pid); rewrite H10 /=.
by done.
simplify => /> Hsim1r Hsim2r.

(*** outputs ***)
progress.
rewrite /simulator /=.
move : Hsim1l Hsim2l Hsim1r Hsim2r H31.
pose rss := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{2} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
pose rs := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{1} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
move => Hsim1l Hsim2l Hsim1r Hsim2r H31.
have gates_l : exists (tl, vwl), (tl, vwl) = eval_gates wl rs xs{2}.
exists (eval_gates wl rs xs{2}).`1 (eval_gates wl rs xs{2}).`2 => /#.
elim gates_l => tl vwl gates_l /=; rewrite -gates_l /=.
have gates_r : exists (tr, vwr), (tr, vwr) = eval_gates wr rs xs{2}.
exists (eval_gates wr rs xs{2}).`1 (eval_gates wr rs xs{2}).`2 => /#.
elim gates_r => tr vwr gates_r /=; rewrite -gates_r /=.
have sgates_l : exists (vwls, tls), (vwls, tls) = simulate_gates wl rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_l => vwls tls sgates_l /=; rewrite -sgates_l /=.
have sgates_r : exists (vwrs, trs), (vwrs, trs) = simulate_gates wr rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_r => vwrs trs sgates_r /=; rewrite -sgates_r /=.
rewrite /eval /= /party_exec /=.
rewrite /input /=.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
have ->: (oget (assoc vwl x0)) = (oget (assoc vwls x0)).
have ->: vwls = (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`1.
smt().
rewrite -Hsim1l.
rewrite !map_assoc //=.
rewrite -gates_l /=.
rewrite !map_assoc //=; first by smt().
have ->: (oget (assoc vwr x0)) = (oget (assoc vwrs x0)).
have ->: vwrs = (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`1.
smt().
rewrite -Hsim1r.
rewrite !map_assoc //=.
rewrite -gates_r /=.
rewrite !map_assoc //=; first by smt().
done.

(***)
rewrite /simulator /=.

move : Hsim1l Hsim2l Hsim1r Hsim2r H31.
pose rss := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{2} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
pose rs := (map
        (fun (pid : pid_t) =>
           (pid,
            map (fun (gid0 : gid_t) => (gid0, get_local_rand pid (oget (assoc grs{1} gid0))))
              (range (np) (np + ns + q)))) ProtocolFunctionality.pid_set).
move => Hsim1l Hsim2l Hsim1r Hsim2r H31.
have gates_l : exists (tl, vwl), (tl, vwl) = eval_gates wl rs xs{2}.
exists (eval_gates wl rs xs{2}).`1 (eval_gates wl rs xs{2}).`2 => /#.
elim gates_l => tl vwl gates_l /=; rewrite -gates_l /=.
have gates_r : exists (tr, vwr), (tr, vwr) = eval_gates wr rs xs{2}.
exists (eval_gates wr rs xs{2}).`1 (eval_gates wr rs xs{2}).`2 => /#.
elim gates_r => tr vwr gates_r /=; rewrite -gates_r /=.
have sgates_l : exists (vwls, tls), (vwls, tls) = simulate_gates wl rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_l => vwls tls sgates_l /=; rewrite -sgates_l /=.
have sgates_r : exists (vwrs, trs), (vwrs, trs) = simulate_gates wr rss (extract_inputs xs{2} cr_) cr_.
exists (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`1 (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`2 => /#.
elim sgates_r => vwrs trs sgates_r /=; rewrite -sgates_r /=.
rewrite /eval /= /party_exec /=.
rewrite /input /=.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=. 
rewrite /rs /rss /rand.
rewrite !map_assoc //=; first 2 by smt().
rewrite -eq_in_map => gid'; progress.
move : (H3 gid').
have ->: gid' \in unzip1 grs{1}.
by rewrite H2 //=. 
progress.
case (is_gate_rands_addition (oget (assoc grs{1} gid'))); progress.
rewrite (rand_eq_add (oget (assoc grs{1} gid')) (oget (assoc grs{2} gid'))).
done.
smt().
smt().
done.
case (is_gate_rands_multiplication (oget (assoc grs{1} gid'))); progress.
move : H33; rewrite H36 /=; progress.
move : (H38 x0).
have ->: x0 \in ProtocolFunctionality.pid_set by smt().
rewrite H10 /=.
done.
case (is_gate_rands_smultiplication (oget (assoc grs{1} gid'))); progress.
rewrite (rand_eq_smul (oget (assoc grs{1} gid')) (oget (assoc grs{2} gid'))).
done.
smt().
smt().
done.
smt().
rewrite !map_assoc //=; first by smt().
rewrite !map_assoc //=; first by smt().
split.
by rewrite !map_assoc //=; first by smt().
split.
have ->: tls = (simulate_gates wl rss (extract_inputs xs{2} cr_) cr_).`2 by smt().
rewrite -Hsim2l.
rewrite !map_assoc //=.
rewrite -gates_l /=.
rewrite !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().
have ->: trs = (simulate_gates wr rss (extract_inputs xs{2} cr_) cr_).`2 by smt().
rewrite -Hsim2r.
rewrite !map_assoc //=.
rewrite -gates_r /=.
rewrite !map_assoc //=; first by smt().
by rewrite !map_assoc //=; first by smt().
qed.

    lemma bgw_weak &m c x aux :
      Pr [GameReal(D,R(RP)).main(c,x,aux) @ &m : res] -
      Pr [GameIdeal(D,R(RP)).main(c,x,aux) @ &m : res] = 0%r.
    proof.
      by have ->: Pr[GameReal(D, R(RP)).main(c, x, aux) @ &m : res] =
               Pr [GameIdeal(D,R(RP)).main(c,x,aux) @ &m : res]
        by byequiv real_ideal_equiv.
    qed.

  end section Security.

end BGWGate.
