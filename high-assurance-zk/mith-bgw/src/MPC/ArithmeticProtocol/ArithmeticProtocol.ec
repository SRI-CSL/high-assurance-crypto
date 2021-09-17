require import Int List.

from General require import ListExt PrimeField FieldPolynomial Utils.

from SecretSharing require import ASecretSharingScheme.
from MPC require import AProtocol AGate.
from Circuit require import ArithmeticCircuit.
from Functionalities require import ArithmeticProtocolFunctionality.
from ArithmeticProtocol require import AdditionGate MultiplicationGate SMultiplicationGate InputGate.

theory ArithmeticProtocol.

  clone import SecretSharingScheme with type secret_t = t, type share_t = t.

  axiom valid_secret_add x y : valid_secret x => valid_secret y => valid_secret (fadd x y).
  axiom valid_secret_mul x y : valid_secret x => valid_secret y => valid_secret (fmul x y).

  clone import AdditionGate with 
    op AdditionFunctionality.SecretSharingScheme.n = n,
    op AdditionFunctionality.SecretSharingScheme.t = t,
    type AdditionFunctionality.SecretSharingScheme.pid_t = pid_t,
    op AdditionFunctionality.SecretSharingScheme.pid_set = pid_set,
    op AdditionFunctionality.SecretSharingScheme.valid_secret = valid_secret,
    type AdditionFunctionality.SecretSharingScheme.share_t = share_t,
    type AdditionFunctionality.SecretSharingScheme.rand_t = rand_t,
    op AdditionFunctionality.SecretSharingScheme.valid_rand = valid_rand,
    op AdditionFunctionality.SecretSharingScheme.share = share,
    op AdditionFunctionality.SecretSharingScheme.public_encoding = public_encoding,
    op AdditionFunctionality.SecretSharingScheme.pub_reconstruct = pub_reconstruct,
    op AdditionFunctionality.SecretSharingScheme.reconstruct = reconstruct,
    op AdditionFunctionality.SecretSharingScheme.get_party_share = get_party_share.

  clone import MultiplicationGate with 
    op MultiplicationFunctionality.SecretSharingScheme.n = n,
    op MultiplicationFunctionality.SecretSharingScheme.t = t,
    type MultiplicationFunctionality.SecretSharingScheme.pid_t = pid_t,
    op MultiplicationFunctionality.SecretSharingScheme.pid_set = pid_set,
    op MultiplicationFunctionality.SecretSharingScheme.valid_secret = valid_secret,
    type MultiplicationFunctionality.SecretSharingScheme.share_t = share_t,
    type MultiplicationFunctionality.SecretSharingScheme.rand_t = AdditionGate.AdditionFunctionality.SecretSharingScheme.rand_t,
    op MultiplicationFunctionality.SecretSharingScheme.valid_rand = AdditionGate.AdditionFunctionality.SecretSharingScheme.valid_rand,
    op MultiplicationFunctionality.SecretSharingScheme.share = share,
    op MultiplicationFunctionality.SecretSharingScheme.public_encoding = public_encoding,
    op MultiplicationFunctionality.SecretSharingScheme.pub_reconstruct = pub_reconstruct,
    op MultiplicationFunctionality.SecretSharingScheme.reconstruct = reconstruct,
    op MultiplicationFunctionality.SecretSharingScheme.get_party_share = get_party_share.

  clone import SMultiplicationGate with 
    op SMultiplicationFunctionality.SecretSharingScheme.n = n,
    op SMultiplicationFunctionality.SecretSharingScheme.t = t,
    type SMultiplicationFunctionality.SecretSharingScheme.pid_t = pid_t,
    op SMultiplicationFunctionality.SecretSharingScheme.pid_set = pid_set,
    op SMultiplicationFunctionality.SecretSharingScheme.valid_secret = valid_secret,
    type SMultiplicationFunctionality.SecretSharingScheme.share_t = share_t,
    type SMultiplicationFunctionality.SecretSharingScheme.rand_t = AdditionGate.AdditionFunctionality.SecretSharingScheme.rand_t,
    op SMultiplicationFunctionality.SecretSharingScheme.valid_rand = AdditionGate.AdditionFunctionality.SecretSharingScheme.valid_rand,
    op SMultiplicationFunctionality.SecretSharingScheme.share = share,
    op SMultiplicationFunctionality.SecretSharingScheme.public_encoding = public_encoding,
    op SMultiplicationFunctionality.SecretSharingScheme.pub_reconstruct = pub_reconstruct,
    op SMultiplicationFunctionality.SecretSharingScheme.reconstruct = reconstruct,
    op SMultiplicationFunctionality.SecretSharingScheme.get_party_share = get_party_share.

  clone import InputGate with 
    op InputFunctionality.SecretSharingScheme.n = n,
    op InputFunctionality.SecretSharingScheme.t = t,
    type InputFunctionality.SecretSharingScheme.pid_t = pid_t,
    op InputFunctionality.SecretSharingScheme.pid_set = pid_set,
    op InputFunctionality.SecretSharingScheme.valid_secret = valid_secret,
    type InputFunctionality.SecretSharingScheme.share_t = share_t,
    type InputFunctionality.SecretSharingScheme.rand_t = AdditionGate.AdditionFunctionality.SecretSharingScheme.rand_t,
    op InputFunctionality.SecretSharingScheme.valid_rand = AdditionGate.AdditionFunctionality.SecretSharingScheme.valid_rand,
    op InputFunctionality.SecretSharingScheme.share = share,
    op InputFunctionality.SecretSharingScheme.public_encoding = public_encoding,
    op InputFunctionality.SecretSharingScheme.pub_reconstruct = pub_reconstruct,
    op InputFunctionality.SecretSharingScheme.reconstruct = reconstruct,
    op InputFunctionality.SecretSharingScheme.get_party_share = get_party_share.

  clone import ArithmeticProtocolFunctionality with
    op SecretSharingScheme.n = n,
    op SecretSharingScheme.t = t,
    type SecretSharingScheme.pid_t = pid_t,
    op SecretSharingScheme.pid_set = pid_set,
    op SecretSharingScheme.valid_secret = valid_secret,
    type SecretSharingScheme.share_t = share_t,
    type SecretSharingScheme.rand_t = AdditionGate.AdditionFunctionality.SecretSharingScheme.rand_t,
    op SecretSharingScheme.valid_rand = AdditionGate.AdditionFunctionality.SecretSharingScheme.valid_rand,
    op SecretSharingScheme.share = share,
    op SecretSharingScheme.public_encoding = public_encoding,
    op SecretSharingScheme.pub_reconstruct = pub_reconstruct,
    op SecretSharingScheme.reconstruct = reconstruct,
    op SecretSharingScheme.get_party_share = get_party_share.
  import ArithmeticCircuit.
  import Circuit.

  type gate_rand_t = [
    | InputRand of InputGate.Gate.rand_t
    | AdditionRand of AdditionGate.Gate.rand_t
    | MultiplicationRand of MultiplicationGate.Gate.rand_t
    | SMultiplicationRand of SMultiplicationGate.Gate.rand_t
    | BadRand
  ].
  op is_gate_rand_input (r : gate_rand_t) : bool =
    with r = InputRand ra => true
    with r = AdditionRand ra => false
    with r = MultiplicationRand rm => false
    with r = SMultiplicationRand rsm => false
    with r = BadRand => false.
  op as_gate_rand_input (r : gate_rand_t) =
    with r = InputRand ri => ri
    with r = AdditionRand ra => witness
    with r = MultiplicationRand rm => witness
    with r = SMultiplicationRand rsm => witness
    with r = BadRand => witness.

  op is_gate_rand_addition (r : gate_rand_t) : bool =
    with r = InputRand ra => false
    with r = AdditionRand ra => true
    with r = MultiplicationRand rm => false
    with r = SMultiplicationRand rsm => false
    with r = BadRand => false.
  op as_gate_rand_addition (r : gate_rand_t) =
    with r = InputRand ra => witness
    with r = AdditionRand ra => ra
    with r = MultiplicationRand rm => witness
    with r = SMultiplicationRand rsm => witness
    with r = BadRand => witness.

  op is_gate_rand_multiplication (r : gate_rand_t) : bool =
    with r = InputRand ra => false  
    with r = AdditionRand ra => false
    with r = MultiplicationRand rm => true
    with r = SMultiplicationRand rsm => false
    with r = BadRand => false.
  op as_gate_rand_multiplication (r : gate_rand_t) =
    with r = InputRand ra => witness
    with r = AdditionRand ra => witness
    with r = MultiplicationRand rm => rm
    with r = SMultiplicationRand rsm => witness
    with r = BadRand => witness.

  op is_gate_rand_smultiplication (r : gate_rand_t) : bool =
    with r = InputRand ra => false  
    with r = AdditionRand ra => false
    with r = MultiplicationRand rm => false
    with r = SMultiplicationRand rsm => true
    with r = BadRand => false.
  op as_gate_rand_smultiplication (r : gate_rand_t) =
    with r = InputRand ra => witness
    with r = AdditionRand ra => witness
    with r = MultiplicationRand rm => witness
    with r = SMultiplicationRand rsm => rsm
    with r = BadRand => witness.

  type rand_t = (gid_t * gate_rand_t) list.
    
  op gates_valid_rand (gg : gates_t) (rs : rand_t) : bool =
    with gg = PInput w => true
    with gg = SInput w => 
      let gr = oget (assoc rs w) in
      is_gate_rand_input gr /\ 
      InputGate.valid_rand (as_gate_rand_input gr)
    with gg = Constant gid c => true
    with gg = Addition gid wl wr => 
      let gr = oget (assoc rs gid) in
      is_gate_rand_addition gr /\ 
      AdditionGate.valid_rand (as_gate_rand_addition gr) /\ 
      gates_valid_rand wl rs /\ gates_valid_rand wr rs
    with gg = Multiplication gid wl wr => 
      let gr = oget (assoc rs gid) in
      is_gate_rand_multiplication gr /\ 
      MultiplicationGate.valid_rand (as_gate_rand_multiplication gr) /\ 
      gates_valid_rand wl rs /\ gates_valid_rand wr rs
    with gg = SMultiplication gid wl wr => 
      let r = oget (assoc rs gid) in
      is_gate_rand_smultiplication r /\ 
      SMultiplicationGate.valid_rand (as_gate_rand_smultiplication r) /\ 
      gates_valid_rand wl rs /\ gates_valid_rand wr rs.
  op valid_rand (c : circuit_t) (r : rand_t) : bool =
    let (topo, gg) = c in gates_valid_rand gg r.
  type rands_t = (pid_t * rand_t) list.
  op valid_rands (c : circuit_t) (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ (forall pid, pid \in pid_set => valid_rand c (oget (assoc rs pid))). 
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).

  type gate_traces_t = [
    | PInputT of t
    | SInputT of wid_t & (pid_t * ((pid_t * InputGate.Gate.msgs_t) list)) list
    | ConstantT of gid_t & t
    | AdditionT of gid_t & (pid_t * ((pid_t * AdditionGate.Gate.msgs_t) list)) list & gate_traces_t & gate_traces_t
    | MultiplicationT of gid_t & (pid_t * ((pid_t * MultiplicationGate.Gate.msgs_t) list)) list & gate_traces_t & gate_traces_t
    | SMultiplicationT of gid_t & (pid_t * ((pid_t * SMultiplicationGate.Gate.msgs_t) list)) list & gate_traces_t & gate_traces_t
  ].
  op is_gate_traces_pinput (lt : gate_traces_t) : bool =
    with lt = PInputT w => true
    with lt = SInputT w tr => false
    with lt = ConstantT gid c => false
    with lt = AdditionT gid tr trl trr => false
    with lt = MultiplicationT gid tr trl trr => false
    with lt = SMultiplicationT gid tr trl trr => false.
  op as_gate_traces_pinput (lt : gate_traces_t) =
    with lt = PInputT w => w
    with lt = SInputT w tr => witness
    with lt = ConstantT gid c => witness
    with lt = AdditionT gid tr trl trr => witness
    with lt = MultiplicationT gid tr trl trr => witness
    with lt = SMultiplicationT gid tr trl trr => witness.
  op is_gate_traces_sinput (lt : gate_traces_t) : bool =
    with lt = PInputT w => false
    with lt = SInputT w tr => true
    with lt = ConstantT gid c => false
    with lt = AdditionT gid tr trl trr => false
    with lt = MultiplicationT gid tr trl trr => false
    with lt = SMultiplicationT gid tr trl trr => false.
  op as_gate_traces_sinput (lt : gate_traces_t) : wid_t =
    with lt = PInputT w => witness
    with lt = SInputT w tr => w
    with lt = ConstantT gid c => witness
    with lt = AdditionT gid tr trl trr => witness
    with lt = MultiplicationT gid tr trl trr => witness
    with lt = SMultiplicationT gid tr trl trr => witness.
  op is_gate_traces_constant (lt : gate_traces_t) : bool =
    with lt = PInputT w => false
    with lt = SInputT w tr => false
    with lt = ConstantT gid c => true
    with lt = AdditionT gid tr trl trr => false
    with lt = MultiplicationT gid tr trl trr => false
    with lt = SMultiplicationT gid tr trl trr => false.
  op as_gate_traces_constant (lt : gate_traces_t) =
    with lt = PInputT w => witness
    with lt = SInputT w tr => witness
    with lt = ConstantT gid c => [c]
    with lt = AdditionT gid tr trl trr => witness
    with lt = MultiplicationT gid tr trl trr => witness
    with lt = SMultiplicationT gid tr trl trr => witness.
  op is_gate_traces_addition (lt : gate_traces_t) : bool =
    with lt = PInputT w => false
    with lt = SInputT w tr => false
    with lt = ConstantT gid c => false
    with lt = AdditionT gid tr trl trr => true
    with lt = MultiplicationT gid tr trl trr => false
    with lt = SMultiplicationT gid tr trl trr => false.
  op as_gate_traces_addition (lt : gate_traces_t) =
    with lt = PInputT w => witness
    with lt = SInputT w tr => witness
    with lt = ConstantT gid c => witness
    with lt = AdditionT gid tr trl trr => (gid,tr,trl,trr)
    with lt = MultiplicationT gid tr trl trr => witness
    with lt = SMultiplicationT gid tr trl trr => witness.
  op is_gate_traces_multiplication (lt : gate_traces_t) : bool =
    with lt = PInputT w => false
    with lt = SInputT w tr => false
    with lt = ConstantT gid c => false
    with lt = AdditionT id tr trl trr => false
    with lt = MultiplicationT id tr trl trr => true
    with lt = SMultiplicationT id tr trl trr => false.
  op as_gate_traces_multiplication (lt : gate_traces_t) =
    with lt = PInputT w => witness
    with lt = SInputT w tr => witness
    with lt = ConstantT gid c => witness
    with lt = AdditionT gid tr trl trr => witness
    with lt = MultiplicationT gid tr trl trr => (gid,tr,trl,trr)
    with lt = SMultiplicationT gid tr trl trr => witness.
  op is_gate_traces_smultiplication (lt : gate_traces_t) : bool =
    with lt = PInputT w => false
    with lt = SInputT w tr => false
    with lt = ConstantT gid c => false
    with lt = AdditionT gid tr trl trr => false
    with lt = MultiplicationT gid tr trl trr => false
    with lt = SMultiplicationT gid tr trl trr => true.
  op as_gate_traces_smultiplication (lt : gate_traces_t) =
    with lt = PInputT w => witness
    with lt = SInputT w tr => witness
    with lt = ConstantT gid c => witness
    with lt = AdditionT gid tr trl trr => witness
    with lt = MultiplicationT gid tr trl trr => witness
    with lt = SMultiplicationT gid tr trl trr => (gid,tr,trl,trr).

  type gate_local_traces_t = [
    | PInputLT of t
    | SInputLT of wid_t & (pid_t * InputGate.Gate.msgs_t) list
    | ConstantLT of gid_t & t
    | AdditionLT of gid_t & (pid_t * AdditionGate.Gate.msgs_t) list & gate_local_traces_t & gate_local_traces_t
    | MultiplicationLT of gid_t & (pid_t * MultiplicationGate.Gate.msgs_t) list & gate_local_traces_t & gate_local_traces_t
    | SMultiplicationLT of gid_t & (pid_t * SMultiplicationGate.Gate.msgs_t) list & gate_local_traces_t & gate_local_traces_t
  ].
  op is_gate_local_traces_pinput (lt : gate_local_traces_t) : bool =
    with lt = PInputLT w => true
    with lt = SInputLT w tr => false
    with lt = ConstantLT gid c => false
    with lt = AdditionLT gid tr trl trr => false
    with lt = MultiplicationLT gid tr trl trr => false
    with lt = SMultiplicationLT gid tr trl trr => false.
  op as_gate_local_traces_pinput (lt : gate_local_traces_t) =
    with lt = PInputLT w => w
    with lt = SInputLT w tr => witness
    with lt = ConstantLT gid c => witness
    with lt = AdditionLT gid tr trl trr => witness
    with lt = MultiplicationLT gid tr trl trr => witness
    with lt = SMultiplicationLT gid tr trl trr => witness.
  op is_gate_local_traces_sinput (lt : gate_local_traces_t) : bool =
    with lt = PInputLT w => false
    with lt = SInputLT w tr => true
    with lt = ConstantLT gid c => false
    with lt = AdditionLT gid tr trl trr => false
    with lt = MultiplicationLT gid tr trl trr => false
    with lt = SMultiplicationLT gid tr trl trr => false.
  op as_gate_local_traces_sinput (lt : gate_local_traces_t) : wid_t =
    with lt = PInputLT w => witness
    with lt = SInputLT w tr => w
    with lt = ConstantLT gid c => witness
    with lt = AdditionLT gid tr trl trr => witness
    with lt = MultiplicationLT gid tr trl trr => witness
    with lt = SMultiplicationLT gid tr trl trr => witness.
  op is_gate_local_traces_constant (lt : gate_local_traces_t) : bool =
    with lt = PInputLT w => false
    with lt = SInputLT w tr => false
    with lt = ConstantLT gid c => true
    with lt = AdditionLT gid tr trl trr => false
    with lt = MultiplicationLT gid tr trl trr => false
    with lt = SMultiplicationLT gid tr trl trr => false.
  op as_gate_local_traces_constant (lt : gate_local_traces_t) =
    with lt = PInputLT w => witness
    with lt = SInputLT w tr => witness
    with lt = ConstantLT gid c => [c]
    with lt = AdditionLT gid tr trl trr => witness
    with lt = MultiplicationLT gid tr trl trr => witness
    with lt = SMultiplicationLT gid tr trl trr => witness.
  op is_gate_local_traces_addition (lt : gate_local_traces_t) : bool =
    with lt = PInputLT w => false
    with lt = SInputLT w tr => false
    with lt = ConstantLT gid c => false
    with lt = AdditionLT gid tr trl trr => true
    with lt = MultiplicationLT gid tr trl trr => false
    with lt = SMultiplicationLT gid tr trl trr => false.
  op as_gate_local_traces_addition (lt : gate_local_traces_t) =
    with lt = PInputLT w => witness
    with lt = SInputLT w tr => witness
    with lt = ConstantLT gid c => witness
    with lt = AdditionLT gid tr trl trr => (gid,tr,trl,trr)
    with lt = MultiplicationLT gid tr trl trr => witness
    with lt = SMultiplicationLT gid tr trl trr => witness.
  op is_gate_local_traces_multiplication (lt : gate_local_traces_t) : bool =
    with lt = PInputLT w => false
    with lt = SInputLT w tr => false
    with lt = ConstantLT gid c => false
    with lt = AdditionLT id tr trl trr => false
    with lt = MultiplicationLT id tr trl trr => true
    with lt = SMultiplicationLT id tr trl trr => false.
  op as_gate_local_traces_multiplication (lt : gate_local_traces_t) =
    with lt = PInputLT w => witness
    with lt = SInputLT w tr => witness
    with lt = ConstantLT gid c => witness
    with lt = AdditionLT gid tr trl trr => witness
    with lt = MultiplicationLT gid tr trl trr => (gid,tr,trl,trr)
    with lt = SMultiplicationLT gid tr trl trr => witness.
  op is_gate_local_traces_smultiplication (lt : gate_local_traces_t) : bool =
    with lt = PInputLT w => false
    with lt = SInputLT w tr => false
    with lt = ConstantLT gid c => false
    with lt = AdditionLT gid tr trl trr => false
    with lt = MultiplicationLT gid tr trl trr => false
    with lt = SMultiplicationLT gid tr trl trr => true.
  op as_gate_local_traces_smultiplication (lt : gate_local_traces_t) =
    with lt = PInputLT w => witness
    with lt = SInputLT w tr => witness
    with lt = ConstantLT gid c => witness
    with lt = AdditionLT gid tr trl trr => witness
    with lt = MultiplicationLT gid tr trl trr => witness
    with lt = SMultiplicationLT gid tr trl trr => (gid,tr,trl,trr).

  op get_local_trace (pid : pid_t) (gt : gate_traces_t) : gate_local_traces_t = 
    with gt = PInputT w => PInputLT w
    with gt = SInputT w tr => SInputLT w (oget (assoc tr pid))
    with gt = ConstantT gid c => ConstantLT gid c
    with gt = AdditionT gid tr trl trr => AdditionLT gid (oget (assoc tr pid)) (get_local_trace pid trl) (get_local_trace pid trr)
    with gt = MultiplicationT gid tr trl trr => MultiplicationLT gid (oget (assoc tr pid)) (get_local_trace pid trl) (get_local_trace pid trr)
    with gt = SMultiplicationT gid tr trl trr => SMultiplicationLT gid (oget (assoc tr pid)) (get_local_trace pid trl) (get_local_trace pid trr).

  type gate_local_msgs_t = [
    | PInputLM of t
    | SInputLM of wid_t & InputGate.msgs_t 
    | ConstantLM of gid_t & t
    | AdditionLM of gid_t & AdditionGate.Gate.msgs_t & gate_local_msgs_t & gate_local_msgs_t
    | MultiplicationLM of gid_t & MultiplicationGate.msgs_t & gate_local_msgs_t & gate_local_msgs_t
    | SMultiplicationLM of gid_t & SMultiplicationGate.msgs_t & gate_local_msgs_t & gate_local_msgs_t
  ].
  op is_gate_local_msgs_pinput (lt : gate_local_msgs_t) : bool =
    with lt = PInputLM w => true
    with lt = SInputLM w tr => false
    with lt = ConstantLM gid c => false
    with lt = AdditionLM gid tr trl trr => false
    with lt = MultiplicationLM gid tr trl trr => false
    with lt = SMultiplicationLM gid tr trl trr => false.
  op as_gate_local_msgs_pinput (lt : gate_local_msgs_t) =
    with lt = PInputLM w => w
    with lt = SInputLM w tr => witness
    with lt = ConstantLM gid c => witness
    with lt = AdditionLM gid tr trl trr => witness
    with lt = MultiplicationLM gid tr trl trr => witness
    with lt = SMultiplicationLM gid tr trl trr => witness.
  op is_gate_local_msgs_sinput (lt : gate_local_msgs_t) : bool =
    with lt = PInputLM w => false
    with lt = SInputLM w tr => true
    with lt = ConstantLM gid c => false
    with lt = AdditionLM gid tr trl trr => false
    with lt = MultiplicationLM gid tr trl trr => false
    with lt = SMultiplicationLM gid tr trl trr => false.
  op as_gate_local_msgs_sinput (lt : gate_local_msgs_t) : wid_t =
    with lt = PInputLM w => witness
    with lt = SInputLM w tr => w
    with lt = ConstantLM gid c => witness
    with lt = AdditionLM gid tr trl trr => witness
    with lt = MultiplicationLM gid tr trl trr => witness
    with lt = SMultiplicationLM gid tr trl trr => witness.
  op is_gate_local_msgs_constant (lt : gate_local_msgs_t) : bool =
    with lt = PInputLM w => false
    with lt = SInputLM w tr => false
    with lt = ConstantLM gid c => true
    with lt = AdditionLM gid tr trl trr => false
    with lt = MultiplicationLM gid tr trl trr => false
    with lt = SMultiplicationLM gid tr trl trr => false.
  op as_gate_local_msgs_constant (lt : gate_local_msgs_t) =
    with lt = PInputLM w => witness
    with lt = SInputLM w tr => witness
    with lt = ConstantLM gid c => [c]
    with lt = AdditionLM gid tr trl trr => witness
    with lt = MultiplicationLM gid tr trl trr => witness
    with lt = SMultiplicationLM gid tr trl trr => witness.
  op is_gate_local_msgs_addition (lt : gate_local_msgs_t) : bool =
    with lt = PInputLM w => false
    with lt = SInputLM w tr => false
    with lt = ConstantLM gid c => false
    with lt = AdditionLM gid tr trl trr => true
    with lt = MultiplicationLM gid tr trl trr => false
    with lt = SMultiplicationLM gid tr trl trr => false.
  op as_gate_local_msgs_addition (lt : gate_local_msgs_t) =
    with lt = PInputLM w => witness
    with lt = SInputLM w tr => witness
    with lt = ConstantLM gid c => witness
    with lt = AdditionLM gid tr trl trr => (gid,tr,trl,trr)
    with lt = MultiplicationLM gid tr trl trr => witness
    with lt = SMultiplicationLM gid tr trl trr => witness.
  op is_gate_local_msgs_multiplication (lt : gate_local_msgs_t) : bool =
    with lt = PInputLM w => false
    with lt = SInputLM w tr => false
    with lt = ConstantLM gid c => false
    with lt = AdditionLM id tr trl trr => false
    with lt = MultiplicationLM id tr trl trr => true
    with lt = SMultiplicationLM id tr trl trr => false.
  op as_gate_local_msgs_multiplication (lt : gate_local_msgs_t) =
    with lt = PInputLM w => witness
    with lt = SInputLM w tr => witness
    with lt = ConstantLM gid c => witness
    with lt = AdditionLM gid tr trl trr => witness
    with lt = MultiplicationLM gid tr trl trr => (gid,tr,trl,trr)
    with lt = SMultiplicationLM gid tr trl trr => witness.
  op is_gate_local_msgs_smultiplication (lt : gate_local_msgs_t) : bool =
    with lt = PInputLM w => false
    with lt = SInputLM w tr => false
    with lt = ConstantLM gid c => false
    with lt = AdditionLM gid tr trl trr => false
    with lt = MultiplicationLM gid tr trl trr => false
    with lt = SMultiplicationLM gid tr trl trr => true.
  op as_gate_local_msgs_smultiplication (lt : gate_local_msgs_t) =
    with lt = PInputLM w => witness
    with lt = SInputLM w tr => witness
    with lt = ConstantLM gid c => witness
    with lt = AdditionLM gid tr trl trr => witness
    with lt = MultiplicationLM gid tr trl trr => witness
    with lt = SMultiplicationLM gid tr trl trr => (gid,tr,trl,trr).

  op get_local_msgs_from (pid : pid_t) (gt : gate_local_traces_t) : gate_local_msgs_t = 
    with gt = PInputLT w => PInputLM w
    with gt = SInputLT w tr => SInputLM w (oget (assoc tr pid))
    with gt = ConstantLT gid c => ConstantLM gid c
    with gt = AdditionLT gid tr trl trr => AdditionLM gid (oget (assoc tr pid)) (get_local_msgs_from pid trl) (get_local_msgs_from pid trr)
    with gt = MultiplicationLT gid tr trl trr => MultiplicationLM gid (oget (assoc tr pid)) (get_local_msgs_from pid trl) (get_local_msgs_from pid trr)
    with gt = SMultiplicationLT gid tr trl trr => SMultiplicationLM gid (oget (assoc tr pid)) (get_local_msgs_from pid trl) (get_local_msgs_from pid trr).

  op get_local_msgs_to (pid : pid_t) (gt : gate_local_traces_t) : gate_local_msgs_t = 
    with gt = PInputLT w => PInputLM w
    with gt = SInputLT w tr => SInputLM w (InputGate.get_messages_to pid tr)
    with gt = ConstantLT gid c => ConstantLM gid c
    with gt = AdditionLT gid tr trl trr => AdditionLM gid (AdditionGate.get_messages_to pid tr) (get_local_msgs_to pid trl) (get_local_msgs_to pid trr)
    with gt = MultiplicationLT gid tr trl trr => MultiplicationLM gid (MultiplicationGate.get_messages_to pid tr) (get_local_msgs_to pid trl) (get_local_msgs_to pid trr)
    with gt = SMultiplicationLT gid tr trl trr => SMultiplicationLM gid (SMultiplicationGate.get_messages_to pid tr) (get_local_msgs_to pid trl) (get_local_msgs_to pid trr).

  type msgs_t = gate_local_msgs_t.

  type in_messages_t = gate_local_traces_t.
  type out_messages_t = gate_local_traces_t.

  op get_messages_from (pid : pid_t) (ims : in_messages_t) : msgs_t = get_local_msgs_from pid ims.
  op get_messages_to (pid : pid_t) (oms : out_messages_t) : msgs_t = get_local_msgs_to pid oms.

  type trace_t = shares_t * in_messages_t.
  type traces_t = (pid_t * trace_t) list.
  op trace (pid : pid_t) (trs : traces_t) : trace_t = oget (assoc trs pid).

  type view_t = input_t * rand_t * trace_t.
  type views_t = (pid_t * view_t) list.
  op view (pid : pid_t) (vs : views_t) : view_t = oget (assoc vs pid).

  op empty_rand = map (fun pid => (pid, ())) pid_set.

  op eval_gates (gg : gates_t) (rs : rands_t) (xs : inputs_t) : gate_traces_t * shares_t =
    with gg = PInput w => 
      let gys = public_encoding (nth witness (pinput (head witness pid_set) xs) w) in
      let tr = PInputT (nth witness (pinput (head witness pid_set) xs) w) in
      (tr, gys)
      
    with gg = SInput w => 
      let ri = map (fun pid => (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w)))) pid_set in
      let vw = map (fun pid => let sec = nth witness (sinput pid xs) w in (pid, sec)) pid_set in
      let gxs = map (fun pid => (pid, ((), oget (assoc vw pid)))) pid_set in
      let (gtr, gys) = InputGate.eval ri gxs in
      let gtrs = SInputT w gtr in

      (gtrs, gys)

    with gg = Constant gid c => 
      let gys = public_encoding c in
      let tr = ConstantT gid c in

      (tr, gys)

    with gg = Addition gid wl wr => 
      let ra = map (fun pid => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set in
      let (tl, vwl) = eval_gates wl rs xs in
      let (tr, vwr) = eval_gates wr rs xs in

      let gxs = map (fun pid => (pid, ((), (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set in

      let (gtr, gys) = AdditionGate.eval ra gxs in
      let gtrs = AdditionT gid gtr tl tr in

      (gtrs, gys)

    with gg = Multiplication gid wl wr => 
      let ra = map (fun pid => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set in
      let (tl, vwl) = eval_gates wl rs xs in
      let (tr, vwr) = eval_gates wr rs xs in

      let gxs = map (fun pid => (pid, ((), (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set in

      let (gtr, gys) = MultiplicationGate.eval ra gxs in
      let gtrs = MultiplicationT gid gtr tl tr in

      (gtrs, gys)

    with gg = SMultiplication gid wl wr => 
      let ra = map (fun pid => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set in
      let (tl, vwl) = eval_gates wl rs xs in
      let (tr, vwr) = eval_gates wr rs xs in

      let gxs = map (fun pid => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set in

      let (gtr, gys) = SMultiplicationGate.eval ra gxs in
      let gtrs = SMultiplicationT gid gtr tl tr in

      (gtrs, gys).

  op eval_circuit (cc : gates_t) (r : rands_t) (x : inputs_t) : gate_traces_t * shares_t = eval_gates cc r x.

  type output_t = AdditionGate.output_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  op protocol (c : circuit_t) (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let (np,ns,m,q) = fst c in
    let cc = snd c in
    let (tr', ys) = eval_circuit cc rs xs in

    let y = reconstruct ys in
    let ys' = map (fun pid => (pid, y)) pid_set in

    let tr = map (fun pid => (pid, get_local_trace pid tr')) pid_set in
    let trs = map (fun pid => (pid, (ys, oget (assoc tr pid)))) pid_set in

    (trs,ys').

  pred pgates_fgates_valid (y_fy : shares_t * t) =
    let (y,fy) = y_fy in unzip1 y = pid_set /\ reconstruct y = fy /\
    valid_secret fy /\ (exists r, SecretSharingScheme.valid_rand r fy /\ share r fy = y).

  pred finput_party_input_tuple_valid (c_fx_x : circuit_t * (t list * t list) * inputs_t) =
    let (c,fx,xs) = c_fx_x in
    let (fxp,fxs) = fx in
    let (np,ns,m,q) = fst c in
    (forall k, 0 <= k < np => 
      let pub = map (fun pid => (pid, nth witness (pinput pid xs) k)) pid_set in
      (forall pid, pid \in pid_set => oget (assoc pub pid) = nth witness fxp k)) /\
    (forall k, np <= k < np+ns => 
      let sec = map (fun pid => (pid, nth witness (sinput pid xs) k)) pid_set in
      (nth fzero fxs k) = sumt (map snd sec)).

  pred pinput_finput_valid (c_x_fx : circuit_t * inputs_t * (t list * t list)) =
    let (c,xs,fx) = c_x_fx in
    let (fxp,fxs) = fx in
    let (np,ns,m,q) = fst c in
    size fxp = np /\ size fxs = np+ns /\
    (forall pid, pid \in pid_set => size (pinput pid xs) = np) /\
    (forall pid, pid \in pid_set => size (sinput pid xs) = np+ns) /\
    finput_party_input_tuple_valid (c,fx,xs).

  pred pinput_finput_valid2 (c_x_fx : circuit_t * inputs_t * (t list * t list)) =
    let (c,xs,fx) = c_x_fx in
    let (fxp,fxs) = fx in
    let (np,ns,m,q) = fst c in
    size fxp = np /\ size fxs = np+ns /\
    (forall pid, pid \in pid_set => size (pinput pid xs) = np) /\
    (forall pid, pid \in pid_set => size (sinput pid xs) = np+ns) /\

    (forall k, 0 <= k < np => 
      let pub = map (fun pid => (pid, nth witness (pinput pid xs) k)) pid_set in
      (forall pid, pid \in pid_set => oget (assoc pub pid) = nth witness fxp k)) /\
    (forall k, np <= k < np+ns => 
      let sec = map (fun pid => (pid, nth witness (sinput pid xs) k)) pid_set in
      (nth fzero fxs k) = reconstruct sec).

  lemma correct_eval_gates (topo : topology_t) (gg : gates_t)
                           (rs : rands_t) (xs : inputs_t) (fx : (t list * t list)) :
    valid_topology topo =>
    ArithmeticCircuit.valid_gates (topo, gg) =>
    valid_inputs_topology topo xs =>
    (all (fun pid => gates_valid_rand gg (oget (assoc rs pid))) pid_set) =>
    pinput_finput_valid ((topo,witness), xs, fx) =>
    pgates_fgates_valid (snd (eval_gates gg rs xs), 
                         ArithmeticProtocolFunctionality.eval_gates gg fx). 
  proof. 
    rewrite /valid_gates /valid_input_gates /valid_smultiplication_gates /valid_gids 
            /valid_topology /valid_inputs_topology /valid_circuit 
            /pid_set /valid_secret /gates_valid_rand
            /share /pinput_finput_valid /finput_party_input_tuple_valid /pgates_fgates_valid
            /valid_secret /sinput /pinput /input /=.
    elim topo => np ns m q /=.
    rewrite !allP /=.
    elim fx => fxp fxs => /> H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17.
    move : H14 H7 H6 H5 H4; elim gg.
      move => /> w H18 H19.
split.
smt(SecretSharingScheme.unzip1_public_encoding).
move : (H16 w).
rewrite H18 H19 /=.
progress.
move : (H4 (head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
simplify.
rewrite !map_assoc //=; first by smt(pid_set_size n_pos).
progress.
rewrite /pinput /input /=.
rewrite H5.
move : (SecretSharingScheme.public_encoding_correct (nth fzero fxp w)).
rewrite /valid_secret /reconstruct /public_encoding.

move : (H10 w).
rewrite H18 H19 /=.
progress.
move : (H6 (head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
simplify.
rewrite !map_assoc //=; first by smt(pid_set_size n_pos).
smt(@List).
have ->: nth fzero fxp w = nth witness fxp w by smt(@List).
rewrite -(H4 (head witness pid_set)).
by smt(pid_set_size n_pos).
move : (H10 w); rewrite H18 H19 /= => H10'; rewrite (H10' (head witness pid_set)).
by smt(pid_set_size n_pos).
have ->: nth witness (pinput (head witness pid_set) xs) w = nth fzero fxp w.
have ->: nth fzero fxp w = nth witness fxp w by smt(@List).
rewrite -(H4 (head witness pid_set)).
by smt(pid_set_size n_pos).
rewrite !map_assoc.
by smt(pid_set_size n_pos).
simplify.
by rewrite /pinput /input /=.
move : (SecretSharingScheme.public_encoding_rand (nth fzero fxp w)).
have ->: SecretSharingScheme.valid_secret (nth fzero fxp w).
have ->: nth fzero fxp w = nth witness fxp w by smt(@List).
rewrite -(H4 (head witness pid_set)).
by smt(pid_set_size n_pos).
move : (H10 w); rewrite H18 H19 /= => H10'; move : (H10' (head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
smt().

(********************** INPUT GATE ***********************)

    move => /> w H18 H19 H20. 
    have : exists gtr gys, (gtr, gys) = eval
       (map
          (fun (pid : pid_t) =>
             (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w))))
          pid_set)
       (map
          (fun (pid : SecretSharingScheme.pid_t) =>
             (pid,
              (tt,
               oget
                 (assoc
                    (map
                       (fun (pid0 : SecretSharingScheme.pid_t) =>
                          (pid0, nth witness (sinput pid0 xs) w)) pid_set)
                    pid)))) pid_set).
exists (eval
       (map
          (fun (pid : pid_t) =>
             (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w))))
          pid_set)
       (map
          (fun (pid : SecretSharingScheme.pid_t) =>
             (pid,
              (tt,
               oget
                 (assoc
                    (map
                       (fun (pid0 : SecretSharingScheme.pid_t) =>
                          (pid0, nth witness (sinput pid0 xs) w)) pid_set)
                    pid)))) pid_set)).`1 (eval
       (map
          (fun (pid : pid_t) =>
             (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w))))
          pid_set)
       (map
          (fun (pid : SecretSharingScheme.pid_t) =>
             (pid,
              (tt,
               oget
                 (assoc
                    (map
                       (fun (pid0 : SecretSharingScheme.pid_t) =>
                          (pid0, nth witness (sinput pid0 xs) w)) pid_set)
                    pid)))) pid_set)).`2.
smt().
progress.
rewrite -H4 /=.
smt.

rewrite -H4 /=.
move : (InputGate.Gate.correct (map
         (fun (pid : pid_t) =>
            (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w))))
         pid_set) (map
         (fun (pid : SecretSharingScheme.pid_t) =>
            (pid,
             (tt,
              oget
                (assoc
                   (map
                      (fun (pid0 : SecretSharingScheme.pid_t) =>
                         (pid0, nth witness (sinput pid0 xs) w)) pid_set) pid))))
         pid_set)).
rewrite /valid_inputs /=.
rewrite -!map_comp /(\o) /= map_id /=.
have ->: pid_set = InputFunctionality.SecretSharingScheme.pid_set by smt().
have ->: (exists (s : t),
    sumt
      (map
         (transpose InputFunctionality.sinput
            (map
               (fun (pid : SecretSharingScheme.pid_t) =>
                  (pid,
                   (tt,
                    oget
                      (assoc
                         (map
                            (fun (pid0 : SecretSharingScheme.pid_t) =>
                               (pid0, nth witness (sinput pid0 xs) w))
                            InputFunctionality.SecretSharingScheme.pid_set)
                         pid))))
               InputFunctionality.SecretSharingScheme.pid_set))
         InputFunctionality.SecretSharingScheme.pid_set) =
    s).
exists (nth fzero fxs w).
rewrite H17.
smt().
rewrite -map_comp /(\o) /=.
congr.
rewrite -eq_in_map => pid; progress.
rewrite /sinput /input.
rewrite !map_assoc //=.
rewrite !map_assoc //=.

simplify.
have -> : (forall (pid : InputFunctionality.SecretSharingScheme.pid_t),
    pid \in InputFunctionality.SecretSharingScheme.pid_set =>
    (InputFunctionality.SecretSharingScheme.valid_secret
       ((InputFunctionality.sinput pid
           (map
              (fun (pid0 : SecretSharingScheme.pid_t) =>
                 (pid0,
                  (tt,
                   oget
                     (assoc
                        (map
                           (fun (pid0_0 : SecretSharingScheme.pid_t) =>
                              (pid0_0, nth witness (sinput pid0_0 xs) w))
                           InputFunctionality.SecretSharingScheme.pid_set)
                        pid0))))
              InputFunctionality.SecretSharingScheme.pid_set))))) <=> true.
progress.
rewrite /sinput /input.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
move : (H13 w).
rewrite H19 H20 /=.
progress.
move : (H6 pid); rewrite H5 /=.
by rewrite !map_assoc //=.
simplify.
have ->: (Gate.valid_rands
    (map
       (fun (pid : pid_t) =>
          (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w))))
       InputFunctionality.SecretSharingScheme.pid_set)).
rewrite /valid_rands.
rewrite -map_comp /(\o) /= map_id.
progress.
rewrite !map_assoc //=.
smt().
rewrite /gate; rewrite -H4 /=.
rewrite /f /=.
rewrite /reconstruct -eq_in_map /=; progress.
rewrite (H5 (head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
rewrite H17.
smt().
rewrite -!map_comp /(\o) /=.
rewrite /sinput /input /=.
congr.
rewrite -eq_in_map => pid; progress.
rewrite !map_assoc //=.
by rewrite !map_assoc //=.

rewrite H17.
smt().

move : (H12 w).
rewrite H19 H20 /=.
by progress.

rewrite -H4 /=.
move : (InputGate.eval_preserves_share (map
         (fun (pid : pid_t) =>
            (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w))))
         pid_set) (map
         (fun (pid : SecretSharingScheme.pid_t) =>
            (pid,
             (tt,
              oget
                (assoc
                   (map
                      (fun (pid0 : SecretSharingScheme.pid_t) =>
                         (pid0, nth witness (sinput pid0 xs) w)) pid_set) pid))))
         pid_set)).
rewrite /valid_inputs /=.
rewrite -!map_comp /(\o) /= map_id /=.
have ->: pid_set = InputFunctionality.SecretSharingScheme.pid_set by smt().
have ->: (exists (s : t),
    sumt
      (map
         (transpose InputFunctionality.sinput
            (map
               (fun (pid : SecretSharingScheme.pid_t) =>
                  (pid,
                   (tt,
                    oget
                      (assoc
                         (map
                            (fun (pid0 : SecretSharingScheme.pid_t) =>
                               (pid0, nth witness (sinput pid0 xs) w))
                            InputFunctionality.SecretSharingScheme.pid_set)
                         pid))))
               InputFunctionality.SecretSharingScheme.pid_set))
         InputFunctionality.SecretSharingScheme.pid_set) =
    s).
exists (nth fzero fxs w).
rewrite H17.
smt().
rewrite -map_comp /(\o) /=.
congr.
rewrite -eq_in_map => pid; progress.
rewrite /sinput /input.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
simplify.
have -> : (forall (pid : InputFunctionality.SecretSharingScheme.pid_t),
    pid \in InputFunctionality.SecretSharingScheme.pid_set =>
    (InputFunctionality.SecretSharingScheme.valid_secret
       ((InputFunctionality.sinput pid
           (map
              (fun (pid0 : SecretSharingScheme.pid_t) =>
                 (pid0,
                  (tt,
                   oget
                     (assoc
                        (map
                           (fun (pid0_0 : SecretSharingScheme.pid_t) =>
                              (pid0_0, nth witness (sinput pid0_0 xs) w))
                           InputFunctionality.SecretSharingScheme.pid_set)
                        pid0))))
              InputFunctionality.SecretSharingScheme.pid_set))))) <=> true.
progress.
rewrite /sinput /input.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
move : (H13 w).
rewrite H19 H20 /=.
progress.
move : (H6 pid); rewrite H5 /=.
by rewrite !map_assoc //=.
simplify.
have ->: (valid_rands
    (map
       (fun (pid : pid_t) =>
          (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w))))
       InputFunctionality.SecretSharingScheme.pid_set)).
rewrite /valid_rands.
rewrite -map_comp /(\o) /= map_id.
progress.
rewrite /rand !map_assoc //=.
smt().
rewrite /gate; rewrite -H4 /=.
rewrite /f /=.
rewrite /valid_rand /reconstruct; progress.
have : reconstruct gys = nth fzero fxs w.
move : (InputGate.Gate.correct (map
         (fun (pid : pid_t) =>
            (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w))))
         pid_set) (map
         (fun (pid : SecretSharingScheme.pid_t) =>
            (pid,
             (tt,
              oget
                (assoc
                   (map
                      (fun (pid0 : SecretSharingScheme.pid_t) =>
                         (pid0, nth witness (sinput pid0 xs) w)) pid_set) pid))))
         pid_set)).
rewrite /valid_inputs /=.
rewrite -!map_comp /(\o) /= map_id /=.
have ->: pid_set = InputFunctionality.SecretSharingScheme.pid_set by smt().
have ->: (exists (s : t),
    sumt
      (map
         (transpose InputFunctionality.sinput
            (map
               (fun (pid : SecretSharingScheme.pid_t) =>
                  (pid,
                   (tt,
                    oget
                      (assoc
                         (map
                            (fun (pid0 : SecretSharingScheme.pid_t) =>
                               (pid0, nth witness (sinput pid0 xs) w))
                            InputFunctionality.SecretSharingScheme.pid_set)
                         pid))))
               InputFunctionality.SecretSharingScheme.pid_set))
         InputFunctionality.SecretSharingScheme.pid_set) =
    s).
exists (nth fzero fxs w).
rewrite H17.
smt().
rewrite -map_comp /(\o) /=.
congr.
rewrite -eq_in_map => pid; progress.
rewrite /sinput /input.
rewrite !map_assoc //=.
rewrite !map_assoc //=.

simplify.
have -> : (forall (pid : InputFunctionality.SecretSharingScheme.pid_t),
    pid \in InputFunctionality.SecretSharingScheme.pid_set =>
    (InputFunctionality.SecretSharingScheme.valid_secret
       ((InputFunctionality.sinput pid
           (map
              (fun (pid0 : SecretSharingScheme.pid_t) =>
                 (pid0,
                  (tt,
                   oget
                     (assoc
                        (map
                           (fun (pid0_0 : SecretSharingScheme.pid_t) =>
                              (pid0_0, nth witness (sinput pid0_0 xs) w))
                           InputFunctionality.SecretSharingScheme.pid_set)
                        pid0))))
              InputFunctionality.SecretSharingScheme.pid_set))))) <=> true.
progress.
rewrite /sinput /input.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
move : (H13 w).
rewrite H19 H20 /=.
progress.
move : (H14 pid); rewrite H7 /=.
by rewrite !map_assoc //=.
simplify.
have ->: (Gate.valid_rands
    (map
       (fun (pid : pid_t) =>
          (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w))))
       InputFunctionality.SecretSharingScheme.pid_set)).
rewrite /valid_rands.
rewrite -map_comp /(\o) /= map_id.
progress.
rewrite !map_assoc //=.
smt().
rewrite /gate; rewrite -H4 /=.
rewrite /f /=.
rewrite /reconstruct -eq_in_map /=; progress.
rewrite (H7 (head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
rewrite H17.
smt().
rewrite -!map_comp /(\o) /=.
rewrite /sinput /input /=.
congr.
rewrite -eq_in_map => pid; progress.
rewrite !map_assoc //=.
by rewrite !map_assoc //=.
smt().

(********************** INPUT GATE ***********************)

      move => /> c; rewrite /valid_constant => /> H18.
split.
smt(SecretSharingScheme.unzip1_public_encoding).
split.
smt(SecretSharingScheme.public_encoding_correct).
smt(SecretSharingScheme.public_encoding_rand).

    move => /> gid wl wr H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30.
    have H31 : exists trl vwl, (trl, vwl) = eval_gates wl rs xs
      by exists (eval_gates wl rs xs).`1 (eval_gates wl rs xs).`2 => /#.
    elim H31 => /> trl vwl H31; rewrite -H31 /=.
    have H32 : exists trr vwr, (trr, vwr) = eval_gates wr rs xs.
      by exists (eval_gates wr rs xs).`1 (eval_gates wr rs xs).`2 => /#.
    elim H32 => /> trr vwr H32; rewrite -H32 /=.
    move : (AdditionGate.Gate.correct (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).
    rewrite /input_pred /sinput /input /pid_set /reconstruct /valid_inputs /pid_set 
            -map_comp /(\o) map_id /valid_secret /valid_rand /share /sinput /input
            /valid_rands /pid_set -map_comp /(\o) map_id /output_pred 
            /pid_set /reconstruct /f /to_foutput /sinput /input /reconstruct /=.
    have ->: reconstruct (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set) = (eval_gates wl (fxp, fxs)).
      have <-: reconstruct (eval_gates wl rs xs).`2 = (eval_gates wl (fxp, fxs)) by smt(). 
      have ->: (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set) = (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwl pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc //=.
      have H33 : unzip1 (eval_gates wl rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wl rs xs).`2); first by by rewrite H33 pid_set_uniq.
      rewrite H33; do 2!congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    have ->: reconstruct (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set) = (eval_gates wr (fxp, fxs)).
      have <-: reconstruct (eval_gates wr rs xs).`2 = (eval_gates wr (fxp, fxs)) by smt().
      have ->: (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set) = (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwr pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc //.
      have H33 : unzip1 (eval_gates wr rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wr rs xs).`2); first by rewrite H33 pid_set_uniq.
      rewrite H33; do 2!congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    have ->: (exists (r : AdditionFunctionality.SecretSharingScheme.rand_t) (s : AdditionFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ valid_rand r s /\ share r s = map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set).
      have H33 : exists (r : ArithmeticProtocol.SecretSharingScheme.rand_t),
                          (valid_rand r (eval_gates wl (fxp, fxs)))%SecretSharingScheme /\
                          share r (eval_gates wl (fxp, fxs)) = (eval_gates wl rs xs).`2 by smt().
      elim H33 => /> r H33 H34.
      exists r (eval_gates wl (fxp, fxs)).
      rewrite H33 H34 /=.
      have ->: (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set) = (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwl pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc.
      have H35 : unzip1 (eval_gates wl rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wl rs xs).`2); first by rewrite H35 pid_set_uniq.
      have ->: valid_secret (eval_gates wl (fxp, fxs)) by smt().
      rewrite H35 /=; congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    have ->: (exists (r : AdditionFunctionality.SecretSharingScheme.rand_t) (s : AdditionFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ valid_rand r s /\ share r s = map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set).
      have H33 : exists (r : ArithmeticProtocol.SecretSharingScheme.rand_t),
                          (valid_rand r (eval_gates wr (fxp, fxs)))%SecretSharingScheme /\
                          share r (eval_gates wr (fxp, fxs)) = (eval_gates wr rs xs).`2 by smt().
      elim H33 => /> r H33 H34.
      exists r (eval_gates wr (fxp, fxs)).
      rewrite H33 H34 /=.
      have ->: (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set) = (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwr pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc.
      have H35 : unzip1 (eval_gates wr rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wr rs xs).`2); first by rewrite H35 pid_set_uniq.
      have ->: valid_secret (eval_gates wr (fxp, fxs)) by smt().
      rewrite H35 /=; congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    rewrite /preim /= -allP.
    have ->: all (fun (x : AdditionFunctionality.SecretSharingScheme.pid_t) => (valid_rand (oget (assoc (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) x)))%AdditionGate.Gate) pid_set.
      rewrite allP; progress.
      by rewrite map_assoc //=; move : (H20 x); rewrite H4 /=. 
    rewrite /share /reconstruct /valid_rand /valid_secret /to_foutput /= => /> H33. 
    move : (AdditionGate.Gate.correct_domain (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)). 
    have H34 : exists (gtr, gys), (gtr, gys) = eval (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set).
      by exists (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).`1
                (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).`2 => /#.
    elim H34 => gtr gys H34; rewrite -H34 /=.
    have ->: unzip1 gys = pid_set.
      have ->: gys = (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).`2 by smt().
      by move : (AdditionGate.eval_domain (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)) => /#. 

have ->: unzip1
  ((gate (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set)
      (map
         (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) =>
            (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)))%AdditionGate.Gate.`2 = AdditionGate.Gate.GateFunctionality.pid_set.
smt.
have ->: unzip1
  ((gate (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set)
      (map
         (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) =>
            (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)))%AdditionGate.Gate.`1 =
AdditionGate.Gate.GateFunctionality.pid_set.
smt.
simplify.

    split.
move : H33.
rewrite /gate /=.
rewrite -H34 /=.
rewrite -eq_in_map.
progress.
rewrite -(H4 (head witness pid_set)).
smt.
done.

    split; first by rewrite valid_secret_add => /#.
move : (AdditionGate.eval_preserves_share (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map
          (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) =>
             (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).
have ->: (AdditionFunctionality.valid_inputs
    (map
       (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) =>
          (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).
rewrite /valid_inputs.
rewrite -!map_comp /(\o) /= map_id /pid_set //=.
    have ->: (exists (r : AdditionFunctionality.SecretSharingScheme.rand_t) (s : AdditionFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ valid_rand r s /\ share r s = map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set).
      have H35 : exists (r : ArithmeticProtocol.SecretSharingScheme.rand_t),
                          (valid_rand r (eval_gates wl (fxp, fxs)))%SecretSharingScheme /\
                          share r (eval_gates wl (fxp, fxs)) = (eval_gates wl rs xs).`2 by smt().
      elim H35 => /> r H35 H36.
      exists r (eval_gates wl (fxp, fxs)).
      rewrite H35 H36 /=.
      have ->: (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set) = (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwl pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc.
      have H37 : unzip1 (eval_gates wl rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wl rs xs).`2); first by rewrite H37 pid_set_uniq.
      have ->: valid_secret (eval_gates wl (fxp, fxs)) by smt().
      rewrite H37 /=; congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    have ->: (exists (r : AdditionFunctionality.SecretSharingScheme.rand_t) (s : AdditionFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ valid_rand r s /\ share r s = map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set).
      have H35 : exists (r : ArithmeticProtocol.SecretSharingScheme.rand_t),
                          (valid_rand r (eval_gates wr (fxp, fxs)))%SecretSharingScheme /\
                          share r (eval_gates wr (fxp, fxs)) = (eval_gates wr rs xs).`2 by smt().
      elim H35 => /> r H35 H36.
      exists r (eval_gates wr (fxp, fxs)).
      rewrite H35 H36 /=.
      have ->: (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set) = (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwr pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc.
      have H37 : unzip1 (eval_gates wr rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wr rs xs).`2); first by rewrite H37 pid_set_uniq.
      have ->: valid_secret (eval_gates wr (fxp, fxs)) by smt().
      rewrite H37 /=; congr.
      by rewrite fun_ext /(==) => /#.
    by simplify.

have ->: valid_rands (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set).
rewrite /valid_rands /=.
rewrite -!map_comp /(\o) /= map_id /pid_set /=.
rewrite /rand.
progress.
rewrite !map_assoc //=.
smt().
simplify.
rewrite -H34 /=.
rewrite /valid_rand /share /reconstruct.
progress.

exists r. 
have : fadd (eval_gates wl (fxp, fxs)) (eval_gates wr (fxp, fxs)) = reconstruct gys.
move : H33.
rewrite /gate -H34 /=.
rewrite /reconstruct -eq_in_map; progress.
rewrite (H6 (head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
done.
smt().



    move => /> gid wl wr H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30.
    have H31 : exists trl vwl, (trl, vwl) = eval_gates wl rs xs
      by exists (eval_gates wl rs xs).`1 (eval_gates wl rs xs).`2 => /#.
    elim H31 => /> trl vwl H31; rewrite -H31 /=.
    have H32 : exists trr vwr, (trr, vwr) = eval_gates wr rs xs.
      by exists (eval_gates wr rs xs).`1 (eval_gates wr rs xs).`2 => /#.
    elim H32 => /> trr vwr H32; rewrite -H32 /=.
    move : (MultiplicationGate.Gate.correct (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).
    rewrite /input_pred /sinput /input /pid_set /reconstruct /valid_inputs /pid_set 
            -map_comp /(\o) map_id /valid_secret /valid_rand /share /sinput /input
            /valid_rands /pid_set -map_comp /(\o) map_id /output_pred 
            /pid_set /reconstruct /gate /f /to_foutput /sinput /input /reconstruct /=.
    have ->: reconstruct (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set) = (eval_gates wl (fxp, fxs)).
      have <-: reconstruct (eval_gates wl rs xs).`2 = (eval_gates wl (fxp, fxs)) by smt(). 
      have ->: (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set) = (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwl pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc //=.
      have H33 : unzip1 (eval_gates wl rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wl rs xs).`2); first by by rewrite H33 pid_set_uniq.
      rewrite H33; do 2!congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    have ->: reconstruct (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set) = (eval_gates wr (fxp, fxs)).
      have <-: reconstruct (eval_gates wr rs xs).`2 = (eval_gates wr (fxp, fxs)) by smt().
      have ->: (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set) = (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwr pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc //.
      have H33 : unzip1 (eval_gates wr rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wr rs xs).`2); first by rewrite H33 pid_set_uniq.
      rewrite H33; do 2!congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    have ->: (exists (r : MultiplicationFunctionality.SecretSharingScheme.rand_t) (s : MultiplicationFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ valid_rand r s /\ share r s = map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set).
      have H33 : exists (r : ArithmeticProtocol.SecretSharingScheme.rand_t),
                          (valid_rand r (eval_gates wl (fxp, fxs)))%SecretSharingScheme /\
                          share r (eval_gates wl (fxp, fxs)) = (eval_gates wl rs xs).`2 by smt().
      elim H33 => /> r H33 H34.
      exists r (eval_gates wl (fxp, fxs)).
      rewrite H33 H34 /=.
      have ->: (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set) = (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwl pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc.
      have H35 : unzip1 (eval_gates wl rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wl rs xs).`2); first by rewrite H35 pid_set_uniq.
      have ->: valid_secret (eval_gates wl (fxp, fxs)) by smt().
      rewrite H35 /=; congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    have ->: (exists (r : MultiplicationFunctionality.SecretSharingScheme.rand_t) (s : MultiplicationFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ valid_rand r s /\ share r s = map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set).
      have H33 : exists (r : ArithmeticProtocol.SecretSharingScheme.rand_t),
                          (valid_rand r (eval_gates wr (fxp, fxs)))%SecretSharingScheme /\
                          share r (eval_gates wr (fxp, fxs)) = (eval_gates wr rs xs).`2 by smt().
      elim H33 => /> r H33 H34.
      exists r (eval_gates wr (fxp, fxs)).
      rewrite H33 H34 /=.
      have ->: (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set) = (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwr pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc.
      have H35 : unzip1 (eval_gates wr rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wr rs xs).`2); first by rewrite H35 pid_set_uniq.
      have ->: valid_secret (eval_gates wr (fxp, fxs)) by smt().
      rewrite H35 /=; congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    rewrite /preim /= -allP.
    have ->: all (fun (x : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (valid_rand (oget (assoc (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) x)))%MultiplicationGate.Gate) pid_set.
      rewrite allP; progress.
      rewrite map_assoc //=; move : (H20 x); rewrite H4 /=. 
    rewrite /share /reconstruct /valid_rand /valid_secret /to_foutput /= => /> H33. 
    move : (MultiplicationGate.Gate.correct_domain (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)). 
    have H34 : exists (gtr, gys), (gtr, gys) = eval (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set).
      by exists (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).`1
                (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).`2 => /#.
    elim H34 => gtr gys H34; rewrite -H34 /=.
    have ->: unzip1 gys = pid_set.
      have ->: gys = (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).`2 by smt().
      by move : (MultiplicationGate.eval_domain (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)) => /#. 

have ->: unzip1
  ((gate (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set)
      (map
         (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) =>
            (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)))%AdditionGate.Gate.`2 = MultiplicationGate.Gate.GateFunctionality.pid_set.
smt.
have ->: unzip1
  ((gate (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set)
      (map
         (fun (pid : MultiplicationFunctionality.SecretSharingScheme.pid_t) =>
            (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)))%AdditionGate.Gate.`1 =
MultiplicationGate.Gate.GateFunctionality.pid_set.
smt.
simplify.

rewrite -eq_in_map.
progress.
rewrite -(H4 (head witness pid_set)).
smt.
done.
by rewrite valid_secret_mul => /#.

move : (MultiplicationGate.eval_preserves_share (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map
          (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) =>
             (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).
have ->: (MultiplicationFunctionality.valid_inputs
    (map
       (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) =>
          (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).
rewrite /valid_inputs.
rewrite -!map_comp /(\o) /= map_id /pid_set //=.
    have ->: (exists (r : AdditionFunctionality.SecretSharingScheme.rand_t) (s : AdditionFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ valid_rand r s /\ share r s = map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set).
      have H35 : exists (r : ArithmeticProtocol.SecretSharingScheme.rand_t),
                          (valid_rand r (eval_gates wl (fxp, fxs)))%SecretSharingScheme /\
                          share r (eval_gates wl (fxp, fxs)) = (eval_gates wl rs xs).`2 by smt().
      elim H35 => /> r H35 H36.
      exists r (eval_gates wl (fxp, fxs)).
      rewrite H35 H36 /=.
      have ->: (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`1)) pid_set) = (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwl pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc.
      have H37 : unzip1 (eval_gates wl rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wl rs xs).`2); first by rewrite H37 pid_set_uniq.
      have ->: valid_secret (eval_gates wl (fxp, fxs)) by smt().
      rewrite H37 /=; congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    have ->: (exists (r : AdditionFunctionality.SecretSharingScheme.rand_t) (s : AdditionFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ valid_rand r s /\ share r s = map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set).
      have H35 : exists (r : ArithmeticProtocol.SecretSharingScheme.rand_t),
                          (valid_rand r (eval_gates wr (fxp, fxs)))%SecretSharingScheme /\
                          share r (eval_gates wr (fxp, fxs)) = (eval_gates wr rs xs).`2 by smt().
      elim H35 => /> r H35 H36.
      exists r (eval_gates wr (fxp, fxs)).
      rewrite H35 H36 /=.
      have ->: (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) pid)).`2.`2)) pid_set) = (map (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwr pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc.
      have H37 : unzip1 (eval_gates wr rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wr rs xs).`2); first by rewrite H37 pid_set_uniq.
      have ->: valid_secret (eval_gates wr (fxp, fxs)) by smt().
      rewrite H37 /=; congr.
      by rewrite fun_ext /(==) => /#.
    by simplify.

have ->: valid_rands (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set).
rewrite /valid_rands /=.
rewrite -!map_comp /(\o) /= map_id /pid_set /=.
rewrite /rand.
progress.
rewrite !map_assoc //=.
smt().
simplify.
rewrite -H34 /=.
rewrite /valid_rand /share /reconstruct.
progress.

exists r. 
have : fmul (eval_gates wl (fxp, fxs)) (eval_gates wr (fxp, fxs)) = reconstruct gys.
rewrite (H4 (head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
done.
smt().


    move => /> gid wl wr H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30.
    have H31 : exists trl vwl, (trl, vwl) = eval_gates wl rs xs
      by exists (eval_gates wl rs xs).`1 (eval_gates wl rs xs).`2 => /#.
    elim H31 => /> trl vwl H31; rewrite -H31 /=.
    have H32 : exists trr vwr, (trr, vwr) = eval_gates wr rs xs.
      by exists (eval_gates wr rs xs).`1 (eval_gates wr rs xs).`2 => /#.
    elim H32 => /> trr vwr H32; rewrite -H32 /=.
    move : (SMultiplicationGate.Gate.correct (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)).
    rewrite /input_pred /sinput /input /pid_set /reconstruct /valid_inputs /pid_set 
            -map_comp /(\o) map_id /valid_secret /valid_rand /share /sinput /input
            /valid_rands /pid_set -map_comp /(\o) map_id /output_pred 
            /pid_set /reconstruct /gate /f /to_foutput /sinput /input /reconstruct /=.
    have ->: reconstruct (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid : pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set) pid)).`2)) SMultiplicationFunctionality.SecretSharingScheme.pid_set) = (eval_gates wr (fxp, fxs)).
      have <-: reconstruct (eval_gates wr rs xs).`2 = (eval_gates wr (fxp, fxs)) by smt(). 
      have ->: (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid : pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set) pid)).`2)) SMultiplicationFunctionality.SecretSharingScheme.pid_set) = (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwr pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc //=.
      have H33 : unzip1 (eval_gates wr rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wr rs xs).`2); first by by rewrite H33 pid_set_uniq.
      rewrite H33; do 2!congr.
      by rewrite fun_ext /(==) => /#.
    simplify.
    have H50 : (exists (s : SMultiplicationFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (SMultiplicationFunctionality.pinput pid (map (fun (pid0 : pid_t) => (pid0, (oget (assoc vwl pid0), (oget (assoc vwr pid0))))) pid_set)))) pid_set = public_encoding s).
       move : H31 H29 H27 H25 H23 H20 H18. case wl => //. 
(*move => c.
progress.
exists c.
rewrite /pinput /input.
rewrite (eq_assoc_map (public_encoding c)).
smt(pid_set_uniq unzip1_public_encoding).
have ->: (unzip1 (public_encoding c)) = pid_set.
smt(pid_set_uniq unzip1_public_encoding).
rewrite -eq_in_map => pid; progress.
rewrite !map_assoc //=.
by rewrite !map_assoc //=.*)
move => gid' c.
progress.
exists c.
rewrite /pinput /input.
rewrite (eq_assoc_map (public_encoding c)).
smt(pid_set_uniq unzip1_public_encoding).
have ->: (unzip1 (public_encoding c)) = pid_set.
smt(pid_set_uniq unzip1_public_encoding).
move : H4; rewrite /valid_constant /valid_secret => H4.
rewrite H4 /=.
rewrite -eq_in_map => pid; progress.
rewrite !map_assoc //=.
by rewrite !map_assoc //=.
    simplify.
    have ->: (exists (r : SMultiplicationFunctionality.SecretSharingScheme.rand_t) (s : SMultiplicationFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ valid_rand r s /\ share r s = map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : pid_t) => (pid0, (oget (assoc vwl pid0), (oget (assoc vwr pid0))))) pid_set) pid)).`2)) pid_set).
      have H33 : exists (r : ArithmeticProtocol.SecretSharingScheme.rand_t),
                          (valid_rand r (eval_gates wr (fxp, fxs)) )%SecretSharingScheme /\
                          share r (eval_gates wr (fxp, fxs)) = (eval_gates wr rs xs).`2 by smt().
      elim H33 => /> r H33 H34.
      exists r (eval_gates wr (fxp, fxs)).
      rewrite H33 H34 /=.
      have ->: map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : pid_t) => (pid0, (oget (assoc vwl pid0), (oget (assoc vwr pid0))))) pid_set) pid)).`2)) pid_set = (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwr pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc.
      have H35 : unzip1 (eval_gates wr rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wr rs xs).`2); first by rewrite H35 pid_set_uniq.
      have ->: valid_secret (eval_gates wr (fxp, fxs)) by smt().
      rewrite H35 /=; congr.
      by rewrite fun_ext /(==) => /#.
    rewrite /valid_secret. rewrite !H50 /=.
    rewrite /preim /= -allP.
    have ->: all (fun (x : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (valid_rand (oget (assoc (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) x)))%AdditionGate.Gate) pid_set.
      rewrite allP; progress.
      by rewrite map_assoc //=; move : (H20 x); rewrite H4 /=. 
    rewrite /share /reconstruct /valid_rand /valid_secret /to_foutput /gate /= => /> H33. 
    move : (SMultiplicationGate.Gate.correct_domain (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)). 
    have H34 : exists (gtr, gys), (gtr, gys) = eval (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set).
      by exists (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)).`1
                (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)).`2 => /#.
    elim H34 => gtr gys H34; rewrite -H34 /=.
    have ->: unzip1 gys = pid_set.
      have ->: gys = (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)).`2 by smt().
      by move : (SMultiplicationGate.eval_domain (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)) => /#. 

have ->: unzip1
  ((gate (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set)
      (map
         (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) =>
            (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)))%AdditionGate.Gate.`2 = SMultiplicationGate.Gate.GateFunctionality.pid_set.
smt.
have ->: unzip1
  ((gate (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set)
      (map
         (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) =>
            (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)))%AdditionGate.Gate.`1 =
SMultiplicationGate.Gate.GateFunctionality.pid_set.
smt.
simplify.

    split.
move : H33.
rewrite /gate /=.
rewrite -H34 /=.
rewrite -eq_in_map.
progress.

      move : H3; rewrite /pub_reconstruct /pinput /input => H3.
have : (pub_reconstruct (head witness SMultiplicationFunctionality.SecretSharingScheme.pid_set)
           (oget
              (assoc
                 (map
                    (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) =>
                       (pid, (oget (assoc vwl pid), (oget (assoc vwr pid), witness<:share_t>)))) pid_set)
                 (head witness SMultiplicationFunctionality.SecretSharingScheme.pid_set))).`1) = (eval_gates wl (fxp, fxs)).
rewrite !map_assoc. smt(@List pid_set_size n_pos).
simplify.

      clear H18 H50 H3. move : H20 H23 H25 H27 H29 H31 H34. case wl => //. 

(*move => c.
progress.
rewrite public_encoding_reconstruct.
smt(@List pid_set_size n_pos).
done.*)

move => gid' c.
progress.
rewrite public_encoding_reconstruct.
smt(@List pid_set_size n_pos).
done.

progress.
rewrite (H4 (head witness SMultiplicationFunctionality.SecretSharingScheme.pid_set)).
have ->: (head witness SMultiplicationFunctionality.SecretSharingScheme.pid_set) \in pid_set.
by smt(@List pid_set_size n_pos).
done.
rewrite /pinputs. rewrite !map_assoc //=.
smt(@List pid_set_size n_pos).
rewrite /SMultiplicationFunctionality.SecretSharingScheme.pub_reconstruct.
rewrite -H5.
congr.
congr.
rewrite !map_assoc /=.
by smt(@List pid_set_size n_pos).
by smt(@List pid_set_size n_pos).
done.

split; first by rewrite valid_secret_mul => /#.


move : (SMultiplicationGate.eval_preserves_share (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set) (map
          (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) =>
             (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)).

have ->: (SMultiplicationFunctionality.valid_inputs
    (map
       (fun (pid : AdditionFunctionality.SecretSharingScheme.pid_t) =>
          (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)).
rewrite /valid_inputs.
rewrite -!map_comp /(\o) /= map_id /pid_set //=.

rewrite H50.
    have ->: (exists (r : SMultiplicationFunctionality.SecretSharingScheme.rand_t) (s : SMultiplicationFunctionality.SecretSharingScheme.secret_t), valid_secret s /\ valid_rand r s /\ share r s = map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : pid_t) => (pid0, (oget (assoc vwl pid0), (oget (assoc vwr pid0))))) pid_set) pid)).`2)) pid_set).
      have H35 : exists (r : ArithmeticProtocol.SecretSharingScheme.rand_t),
                          (valid_rand r (eval_gates wr (fxp, fxs)) )%SecretSharingScheme /\
                          share r (eval_gates wr (fxp, fxs)) = (eval_gates wr rs xs).`2 by smt().
      elim H35 => /> r H35 H36.
      exists r (eval_gates wr (fxp, fxs)).
      rewrite H35 H36 /=.
      have ->: map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, (oget (assoc (map (fun (pid0 : pid_t) => (pid0, (oget (assoc vwl pid0), (oget (assoc vwr pid0))))) pid_set) pid)).`2)) pid_set = (map (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid, ((oget (assoc vwr pid))))) pid_set).
        rewrite -eq_in_map; progress.
        by rewrite map_assoc.
      have H37 : unzip1 (eval_gates wr rs xs).`2 = pid_set by smt().
      rewrite (eq_assoc_map (eval_gates wr rs xs).`2); first by rewrite H37 pid_set_uniq.
      have ->: valid_secret (eval_gates wr (fxp, fxs)) by smt().
      rewrite H37 /=; congr.
      by rewrite fun_ext /(==) => /#.
done.

have ->: valid_rands (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set).
rewrite /valid_rands /=.
rewrite -!map_comp /(\o) /= map_id /pid_set /=.
rewrite /rand.
progress.
rewrite !map_assoc //=.
smt().
simplify.
rewrite -!H34 /=.
rewrite /valid_rand /share /reconstruct.
progress.
move : H33; rewrite -H34 /=.
progress.

exists r. 
move : H6; rewrite -eq_in_map.
progress.
move : (H6(head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
simplify.
(*smt.
have : fmul (eval_gates wl (fxp, fxs)) (eval_gates wr (fxp, fxs)) = reconstruct gys.
rewrite (H4 (head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
done.
smt().

rewrite H4 /= -H5 /=.
move : H33; rewrite /gate /=.
rewrite -H34 /=.
rewrite -eq_in_map.
rewrite /reconstruct /=.
progress.
rewrite (H6 (head witness pid_set)).
smt(@List n_pos pid_set_size).*)

have : (pub_reconstruct (head witness SMultiplicationFunctionality.SecretSharingScheme.pid_set)
           (oget
              (assoc
                 (map
                    (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) =>
                       (pid, (oget (assoc vwl pid), (oget (assoc vwr pid), witness<:share_t>)))) pid_set)
                 (head witness SMultiplicationFunctionality.SecretSharingScheme.pid_set))).`1) = (eval_gates wl (fxp, fxs)).
rewrite !map_assoc. smt(@List pid_set_size n_pos).
simplify.

      clear H18 H50 H3. move : H20 H23 H25 H27 H29 H31 H34. case wl => //. 

(*move => c.
progress.
rewrite public_encoding_reconstruct.
smt(@List pid_set_size n_pos).
done.*)

move => gid' c.
progress.
rewrite public_encoding_reconstruct.
smt(@List pid_set_size n_pos).
done.

rewrite /pinputs /=.
progress.
rewrite /pinput /input /=.
rewrite /pub_reconstruct.
rewrite -H7.
move : H14.
rewrite !map_assoc //=.
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
rewrite !map_assoc //=.
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
smt().

move : (H6(head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
simplify.
(*smt.
have : fmul (eval_gates wl (fxp, fxs)) (eval_gates wr (fxp, fxs)) = reconstruct gys.
rewrite (H4 (head witness pid_set)).
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
done.
smt().

rewrite H4 /= -H5 /=.
move : H33; rewrite /gate /=.
rewrite -H34 /=.
rewrite -eq_in_map.
rewrite /reconstruct /=.
progress.
rewrite (H6 (head witness pid_set)).
smt(@List n_pos pid_set_size).*)

have : (pub_reconstruct (head witness SMultiplicationFunctionality.SecretSharingScheme.pid_set)
           (oget
              (assoc
                 (map
                    (fun (pid : SMultiplicationFunctionality.SecretSharingScheme.pid_t) =>
                       (pid, (oget (assoc vwl pid), (oget (assoc vwr pid), witness<:share_t>)))) pid_set)
                 (head witness SMultiplicationFunctionality.SecretSharingScheme.pid_set))).`1) = (eval_gates wl (fxp, fxs)).
rewrite !map_assoc. smt(@List pid_set_size n_pos).
simplify.

      clear H18 H50 H3. move : H20 H23 H25 H27 H29 H31 H34. case wl => //. 

(*move => c.
progress.
rewrite public_encoding_reconstruct.
smt(@List pid_set_size n_pos).
done.*)

move => gid' c.
progress.
rewrite public_encoding_reconstruct.
smt(@List pid_set_size n_pos).
done.

rewrite /pinputs /=.
progress.
rewrite /pinput /input /=.
rewrite /pub_reconstruct.
rewrite -H7.
move : H14.
rewrite !map_assoc //=.
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
rewrite !map_assoc //=.
have ->: head witness pid_set \in pid_set by smt(pid_set_size n_pos).
done.
smt().
qed.

  lemma correct (c : circuit_t) (rs : rands_t) (xs : inputs_t) :
    ProtocolFunctionality.valid_inputs c xs =>
    valid_rands c rs =>
    snd (protocol c rs xs) = f c xs.
  proof.
    rewrite /valid_inputs /valid_inputs_topology /valid_rands.
    elim c => topo gg /=.
    elim topo => np ns m q /=.
    rewrite /valid_circuit /= /valid_gates /pinput /input /valid_secret /valid_rand
            /valid_rand_circuit /= /eval_circuit; progress.
    rewrite /f /protocol /= /pid_set /=; (*-eq_in_map => pid*) progress.
    rewrite /eval_circuit -!map_comp /(\o) /pinput /sinput /input; (*-eq_in_map => g;*) progress.
    move : (correct_eval_gates (np,ns,m,q) gg rs xs ((oget (assoc xs (head witness pid_set))).`1, map (fun (x : int) => ((sumt (map snd (map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc xs pid0)).`2 x)) pid_set)))%SecretSharingScheme)) (range 0 (np+ns)))).
    rewrite H.
    have ->: ArithmeticCircuit.valid_gates ((np, ns, m, q), gg) 
      by rewrite /valid_gates /= => /#.
    have ->: valid_inputs_topology (np, ns, m, q) xs. 

      rewrite /valid_inputs_topology /pinput /sinput /input  /=; progress. smt().
      move : (H7 k); rewrite H13 H14 /=; progress => /#.
      move : (H9 k); rewrite H13 H14 /=; progress => /#.
      move : (H10 k); rewrite H13 H14 /= /sinput /input /=; progress. smt().
      have ->: all (fun (pid : pid_t) => gates_valid_rand gg (oget (assoc rs pid))) pid_set by rewrite allP.
    have ->: pinput_finput_valid (((np, ns, m, q), witness), xs, ((oget (assoc xs (head witness pid_set))).`1, map (fun (x : int) => (sumt (map snd (map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, nth witness (oget (assoc xs pid0)).`2 x)) pid_set)))) (range 0 (np+ns)))).
      rewrite /pinput_finput_valid /= size_map size_range /= /max.
      have ->: 0 < np+ns by smt().
      simplify; rewrite H5; first by rewrite headP pid_set_size; smt(n_pos).
      rewrite /pinput /sinput /input /=.
      split; first by smt().
      split; first by smt().
      rewrite /finput_party_input_tuple_valid /=; split.
        progress; rewrite map_assoc // !Core.oget_some /= /pinput /input /=.
        move : (H8 k); rewrite H13 H14 /=.
        progress; move : H16; rewrite allP; progress.
        move : (H16 (pid, nth witness (oget (assoc xs pid)).`1 k)). 
        rewrite mapP.
        have ->: (exists (x : SecretSharingScheme.pid_t), (x \in pid_set) /\ (pid, nth witness (oget (assoc xs pid)).`1 k) = (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc xs pid1)).`1 k)) x)
          by exists pid; rewrite H15 => //.
        simplify => H18.
        move : (H16 ((head witness pid_set), 
                nth fzero (oget (assoc xs (head witness pid_set))).`1 k)). 
        rewrite mapP.
        have ->: (exists (x : SecretSharingScheme.pid_t), (x \in pid_set) /\ (head witness pid_set, nth fzero (oget (assoc xs (head witness pid_set))).`1 k) = (fun (pid1 : SecretSharingScheme.pid_t) => (pid1, nth witness (oget (assoc xs pid1)).`1 k)) x).
          exists (head witness pid_set).
          have ->: head witness pid_set \in pid_set by rewrite headP pid_set_size; smt(n_pos).
          simplify; move : (H5 (head witness pid_set)).
          have ->: head witness pid_set \in pid_set.
            have : size pid_set = n by apply pid_set_size.
            by smt(@List n_pos).
          by smt(@List).
        by smt().
      progress; move : (H9 k); rewrite H13 H14 /=; progress.
      rewrite (*-H17 /=*) (nth_map witness fzero); first by rewrite size_range /max /= /#.
      simplify.
      have ->: (nth witness (range 0 (np+ns)) k) = k by smt(@Range). 
done.      

    rewrite /pgates_fgates_valid /=; progress. rewrite -H13.
    have H26 : exists (tr', y'), (tr', y') = eval_gates gg rs xs
      by exists (eval_gates gg rs xs).`1 (eval_gates gg rs xs).`2 => /#.
    elim H26 => tr' y' /= H26; rewrite -H26 /=.

have ->: (unzip1 y') = pid_set by smt().
rewrite -H13.
rewrite -eq_in_map; progress.
rewrite H13.
have ->: y' = (eval_gates gg rs xs).`2 by smt().
rewrite H14.
done.
  qed.

  op local_output_gates (pid : pid_t) (x : input_t) 
                        (r : rand_t) (im : gate_local_traces_t) : share_t =
    with im = PInputLT c => oget (assoc (public_encoding c) pid)
    with im = SInputLT w tr => 
      let ri = as_gate_rand_input (oget (assoc r w)) in
      InputGate.local_output_share pid ((), nth witness x.`2 w) ri tr
    with im = ConstantLT gid c => oget (assoc (public_encoding c) pid)
    with im = AdditionLT gid tr trl trr => 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in
      let ra = as_gate_rand_addition (oget (assoc r gid)) in
      AdditionGate.local_output_share pid ((),(vl,vr)) ra tr
    with im = MultiplicationLT gid tr trl trr => 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in
      let rm = as_gate_rand_multiplication (oget (assoc r gid)) in
      MultiplicationGate.local_output_share pid ((),(vl,vr)) rm tr
    with im = SMultiplicationLT gid tr trl trr => 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in
      let rm = as_gate_rand_smultiplication (oget (assoc r gid)) in
      SMultiplicationGate.local_output_share pid (vl,(vr)) rm tr.

  op valid_trace_gates (g : gates_t) (gtr : gate_local_traces_t) : bool =
    with g = PInput w => is_gate_local_traces_pinput gtr
    with g = SInput w => is_gate_local_traces_sinput gtr
    with g = Constant gid c => is_gate_local_traces_constant gtr
    with g = Addition gid wl wr =>
      is_gate_local_traces_addition gtr &&
        let (gid', gtr', tl, tr) = as_gate_local_traces_addition gtr in
        valid_trace_gates wl tl /\ valid_trace_gates wr tr
    with g = Multiplication gid wl wr =>
      is_gate_local_traces_multiplication gtr &&
        let (gid', gtr', tl, tr) = as_gate_local_traces_multiplication gtr in
        valid_trace_gates wl tl /\ valid_trace_gates wr tr
    with g = SMultiplication gid wl wr =>
      is_gate_local_traces_smultiplication gtr &&
        let (gid', gtr', tl, tr) = as_gate_local_traces_smultiplication gtr in
        valid_trace_gates wl tl /\ valid_trace_gates wr tr.

  op valid_circuit_trace (c : circuit_t) (ims : in_messages_t) : bool =
    let (topo, gg) = c in valid_trace_gates gg ims.

  lemma zip_map_assoc s (f : 'a -> 'b) :
    zip s (map f s) = map (fun x => (x, f x)) s by elim s. 

  lemma valid_trace_protocol (c : circuit_t) (rs : rands_t) (xs : inputs_t) (pid : pid_t) : 
    pid \in pid_set =>
    let (trs, ys) = protocol c rs xs in
    valid_circuit_trace c (trace pid trs).`2.
  proof.
    move => H.
    have : exists (trs, ys), (trs, ys) = protocol c rs xs by smt().
    move => H0; elim H0 => trs ys H0; rewrite -H0 /=.
    have ->: trs = (protocol c rs xs).`1 by smt().
    rewrite /valid_trace /=.
    move : H0; elim c => topo gg /=.
    elim topo => n m q H0 /=.
    rewrite /trace /protocol /eval_circuit /=.
    have H2 : exists (tr', y'), (tr', y') = eval_gates gg rs xs
      by exists (eval_gates gg rs xs).`1 (eval_gates gg rs xs).`2 => /#.
    elim H2 => tr' y' /= H2; rewrite -H2 /=.
    rewrite !map_assoc //= !map_assoc //=.
    have ->: tr' = (eval_gates gg rs xs).`1 by smt().
    progress. by clear H2; elim gg => /#.
  qed.

  op local_output (c : circuit_t) (pid : pid_t) (v : view_t) : output_t =
    let (x,r,tr) = v in
    let (topo, gg) = c in 
    let (ys,ims) = tr in
    if valid_circuit_trace c ims /\ local_output_gates pid x r ims = oget (assoc ys pid) then
      reconstruct ys
    else witness.

  lemma local_output_correct_gates (topo : topology_t) (g : gates_t) (pid : pid_t) 
                                   (xs : inputs_t) (rs : rands_t) :
    pid \in pid_set =>
    (oget (assoc (eval_gates g rs xs).`2 pid)) = 
    (local_output_gates pid (input pid xs) (rand pid rs) (get_local_trace pid (eval_gates g rs xs).`1)).
  proof.
    move => hpid; elim g.

      * by move => w /=.

      * move => w /=.
        move : (InputGate.local_output_share_correct pid (map (fun (pid0 : SecretSharingScheme.pid_t) => (pid0, (tt, oget (assoc (map
                          (fun (pid1 : SecretSharingScheme.pid_t) =>
                             (pid1, nth witness (sinput pid1 xs) w)) pid_set)
                       pid0)))) pid_set) (map (fun (pid0 : pid_t) => (pid0, as_gate_rand_input (oget (assoc (oget (assoc rs pid0)) w)))) pid_set)).
rewrite hpid /=.
have H : exists tr y, (tr, y) = eval
    (map
       (fun (pid0 : pid_t) =>
          (pid0, as_gate_rand_input (oget (assoc (oget (assoc rs pid0)) w))))
       pid_set)
    (map
       (fun (pid0 : SecretSharingScheme.pid_t) =>
          (pid0,
           (tt,
            oget
              (assoc
                 (map
                    (fun (pid1 : SecretSharingScheme.pid_t) =>
                       (pid1, nth witness (sinput pid1 xs) w)) pid_set) pid0))))
       pid_set).
exists (eval
    (map
       (fun (pid0 : pid_t) =>
          (pid0, as_gate_rand_input (oget (assoc (oget (assoc rs pid0)) w))))
       pid_set)
    (map
       (fun (pid0 : SecretSharingScheme.pid_t) =>
          (pid0,
           (tt,
            oget
              (assoc
                 (map
                    (fun (pid1 : SecretSharingScheme.pid_t) =>
                       (pid1, nth witness (sinput pid1 xs) w)) pid_set) pid0))))
       pid_set)).`1 (eval
    (map
       (fun (pid0 : pid_t) =>
          (pid0, as_gate_rand_input (oget (assoc (oget (assoc rs pid0)) w))))
       pid_set)
    (map
       (fun (pid0 : SecretSharingScheme.pid_t) =>
          (pid0,
           (tt,
            oget
              (assoc
                 (map
                    (fun (pid1 : SecretSharingScheme.pid_t) =>
                       (pid1, nth witness (sinput pid1 xs) w)) pid_set) pid0))))
       pid_set)).`2. by smt().
elim H => tr y H.
rewrite -H /=.
rewrite /input /rand.
rewrite !map_assoc //=.
rewrite !map_assoc //=.

      * by move => gid c /=.

      (* Addition *)
      * move => /= gid wl wr H H0.
        have H1: exists tl vwl, (tl,vwl) = eval_gates wl rs xs by exists (eval_gates wl rs xs).`1 (eval_gates wl rs xs).`2 => /#.
        elim H1 => tl vwl H1; rewrite -H1.
        have H2 : exists tr vwr, (tr,vwr) = eval_gates wr rs xs by exists (eval_gates wr rs xs).`1 (eval_gates wr rs xs).`2 => /#.
        elim H2 => tr vwr H2; rewrite -H2.
        move : (AdditionGate.local_output_share_correct pid (map (fun (pid0 : AdditionFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) (map (fun (pid0 : pid_t) => (pid0, as_gate_rand_addition (oget (assoc (oget (assoc rs pid0)) gid)))) pid_set)).
        by rewrite /pid_set /= /gate /= /output /input /rand 
                /local_output !map_assoc //= hpid /= /#. 

      (* Multiplication *)
      * move => /= gid wl wr H H0.
        have H1: exists tl vwl, (tl,vwl) = eval_gates wl rs xs by exists (eval_gates wl rs xs).`1 (eval_gates wl rs xs).`2 => /#.
        elim H1 => tl vwl H1; rewrite -H1.
        have H2 : exists tr vwr, (tr,vwr) = eval_gates wr rs xs by exists (eval_gates wr rs xs).`1 (eval_gates wr rs xs).`2 => /#.
        elim H2 => tr vwr H2; rewrite -H2.
        move : (MultiplicationGate.local_output_share_correct pid (map (fun (pid0 : MultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid0, (tt, (oget (assoc vwl pid0), oget (assoc vwr pid0))))) pid_set) (map (fun (pid0 : pid_t) => (pid0, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid0)) gid)))) pid_set)).
        by rewrite /pid_set /= /gate /= /output /input /rand 
                /local_output !map_assoc //= hpid /= => /#. 

      (* SMultiplication *)
      * move => /= gid wl wr H H0.
        have H1: exists tl vwl, (tl,vwl) = eval_gates wl rs xs by exists (eval_gates wl rs xs).`1 (eval_gates wl rs xs).`2 => /#.
        elim H1 => tl vwl H1; rewrite -H1.
        have H2 : exists tr vwr, (tr,vwr) = eval_gates wr rs xs by exists (eval_gates wr rs xs).`1 (eval_gates wr rs xs).`2 => /#.
        elim H2 => tr vwr H2; rewrite -H2.
        move : (SMultiplicationGate.local_output_share_correct pid (map (fun (pid0 : SMultiplicationFunctionality.SecretSharingScheme.pid_t) => (pid0, (oget (assoc vwl pid0), (oget (assoc vwr pid0))))) pid_set) (map (fun (pid0 : pid_t) => (pid0, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid0)) gid)))) pid_set)).
        by rewrite /pid_set /= /gate /= /output /input /rand 
                /local_output !map_assoc //= hpid /= => /#. 
  qed.

  lemma local_output_correct (c : circuit_t) (pid : pid_t) (xs : inputs_t) (rs : rands_t) :
    pid \in pid_set =>
    let (tr, y) = protocol c rs xs in
    AdditionGate.output pid y = local_output c pid (input pid xs, rand pid rs, trace pid tr). 
  proof.
    rewrite /local_output /output => /> H tr y; progress.
    move : H0; elim c => topo gg /=; progress.
    rewrite /trace; have : exists (ys, ims), (ys, ims) = oget (assoc tr pid)
      by exists (oget (assoc tr pid)).`1 (oget (assoc tr pid)).`2 => /#.
    progress; rewrite -H1 /=.
    have ->: valid_circuit_trace (topo, gg) ims. 
move : (valid_trace_protocol (topo, gg) rs xs pid).
by rewrite H /= /#.
    rewrite /trace /=.
    have ->: local_output_gates pid (input pid xs) (rand pid rs) ims = oget (assoc ys pid).
      move : H0; rewrite /protocol /=; elim topo => np ns m q /=.
      rewrite /eval_circuit /=.
      have H2 : exists (tr', y'), (tr', y') = eval_gates gg rs xs
        by exists (eval_gates gg rs xs).`1 (eval_gates gg rs xs).`2 => /#.
      elim H2 => tr' y' /= H2; rewrite -H2; progress.
      move : H1; rewrite !map_assoc //= !map_assoc //=.
      have ->: y' = (eval_gates gg rs xs).`2 by smt().
      have ->: tr' = (eval_gates gg rs xs).`1 by smt().
      progress.
      by rewrite -(local_output_correct_gates (np,ns,m,q) gg pid xs rs) /=. 
    simplify; move : H0 H1.
    rewrite /protocol /=; elim topo => np ns m q /=.
    rewrite /eval_circuit /=.
    have H2 : exists (tr', y'), (tr', y') = eval_gates gg rs xs
      by exists (eval_gates gg rs xs).`1 (eval_gates gg rs xs).`2 => /#.
    elim H2 => tr' y' /= H2; rewrite -H2; progress.
    by move : H0; rewrite !map_assoc //= !map_assoc //=.
  qed.

  op out_messages_gates (pid : pid_t) (x : input_t) 
                        (r : rand_t) (im : gate_local_traces_t) : gate_local_traces_t =
    with im = PInputLT w => PInputLT w
    with im = SInputLT w tr => 
      let ri = as_gate_rand_input (oget (assoc r w)) in
      SInputLT w (InputGate.out_messages_in_messages pid ((), nth witness x.`2 w) ri tr)
    with im = ConstantLT gid c => ConstantLT gid c
    with im = AdditionLT gid tr trl trr => 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in

      let owl = out_messages_gates pid x r trl in
      let owr = out_messages_gates pid x r trr in

      let ra = as_gate_rand_addition (oget (assoc r gid)) in
      AdditionLT gid (AdditionGate.out_messages_in_messages pid ((),(vl,vr)) ra tr) owl owr
    with im = MultiplicationLT gid tr trl trr => 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in

      let owl = out_messages_gates pid x r trl in
      let owr = out_messages_gates pid x r trr in

      let rm = as_gate_rand_multiplication (oget (assoc r gid)) in
      MultiplicationLT gid (MultiplicationGate.out_messages_in_messages pid ((),(vl,vr)) rm tr) owl owr
    with im = SMultiplicationLT gid tr trl trr => 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in

      let owl = out_messages_gates pid x r trl in
      let owr = out_messages_gates pid x r trr in

      let rm = as_gate_rand_smultiplication (oget (assoc r gid)) in
      SMultiplicationLT gid (SMultiplicationGate.out_messages_in_messages pid (vl,(vr)) rm tr) owl owr.

  op out_messages (c : circuit_t) (pid : pid_t) (v : view_t) : out_messages_t =
    let (topo, gg) = c in 
    let (x,r,tr) = v in
    if valid_circuit_trace c tr.`2 then out_messages_gates pid x r tr.`2
    else witness.

  lemma messages_gates_consistency (g : gates_t) (i j : pid_t) 
                                   (xs : inputs_t) (rs : rands_t) :
    i \in pid_set => j \in pid_set =>
    get_local_msgs_to j (out_messages_gates i (input i xs) (rand i rs) (get_local_trace i (eval_gates g rs xs).`1)) = get_local_msgs_from i (get_local_trace j (eval_gates g rs xs).`1).
  proof.
    progress; elim g.
    
      * by move => w />. 

      * move => w />.

        move : (InputGate.Gate.messages_consistency i j (map (fun (pid : pid_t) => (pid, (tt, oget
                       (assoc
                          (map
                             (fun (pid0 : SecretSharingScheme.pid_t) =>
                                (pid0, nth witness (sinput pid0 xs) w))
                             pid_set) pid)))) pid_set) (map (fun (pid : pid_t) => (pid, as_gate_rand_input (oget (assoc (oget (assoc rs pid)) w)))) pid_set)).

rewrite H H0 /=.
have H1 : exists tr y, (tr, y) = eval
    (map
       (fun (pid0 : pid_t) =>
          (pid0, as_gate_rand_input (oget (assoc (oget (assoc rs pid0)) w))))
       pid_set)
    (map
       (fun (pid0 : SecretSharingScheme.pid_t) =>
          (pid0,
           (tt,
            oget
              (assoc
                 (map
                    (fun (pid1 : SecretSharingScheme.pid_t) =>
                       (pid1, nth witness (sinput pid1 xs) w)) pid_set) pid0))))
       pid_set).
exists (eval
    (map
       (fun (pid0 : pid_t) =>
          (pid0, as_gate_rand_input (oget (assoc (oget (assoc rs pid0)) w))))
       pid_set)
    (map
       (fun (pid0 : SecretSharingScheme.pid_t) =>
          (pid0,
           (tt,
            oget
              (assoc
                 (map
                    (fun (pid1 : SecretSharingScheme.pid_t) =>
                       (pid1, nth witness (sinput pid1 xs) w)) pid_set) pid0))))
       pid_set)).`1 (eval
    (map
       (fun (pid0 : pid_t) =>
          (pid0, as_gate_rand_input (oget (assoc (oget (assoc rs pid0)) w))))
       pid_set)
    (map
       (fun (pid0 : SecretSharingScheme.pid_t) =>
          (pid0,
           (tt,
            oget
              (assoc
                 (map
                    (fun (pid1 : SecretSharingScheme.pid_t) =>
                       (pid1, nth witness (sinput pid1 xs) w)) pid_set) pid0))))
       pid_set)).`2. by smt().
elim H1 => tr y H1.
rewrite /Gate.gate /gate -H1 /=.
rewrite /input /rand /trace.
rewrite !map_assoc //=.
rewrite !map_assoc //=.

      * by move => w />. 
      * move => w wl wr; progress.
        have H3: exists tl vwl, (tl,vwl) = eval_gates wl rs xs by exists (eval_gates wl rs xs).`1 (eval_gates wl rs xs).`2 => /#.
        elim H3 => tl vwl H3; rewrite -H3.
        have H4 : exists tr vwr, (tr,vwr) = eval_gates wr rs xs by exists (eval_gates wr rs xs).`1 (eval_gates wr rs xs).`2 => /#.
        elim H4 => tr vwr H4; rewrite -H4 /=.
        move : (AdditionGate.Gate.messages_consistency i j (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set) (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) w)))) pid_set)).
        rewrite /pid_set /gate /= H H0 /= /input /rand /trace
                !map_assoc //=.
        have : exists (tr0, ys), (tr0, ys) = eval (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) w)))) pid_set) (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set) 
          by exists (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) w)))) pid_set) (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).`1
                    (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) w)))) pid_set) (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).`2 => /#.
        progress; move : H6; rewrite -H5 /=.
        rewrite !map_assoc //= /out_messages /get_messages_to /get_messages_from.
        move : (local_output_correct_gates witness wl i xs rs); rewrite H /=.
        move : (local_output_correct_gates witness wr i xs rs); rewrite H /=.
        have ->: tl = (eval_gates wl rs xs).`1 by smt().
        have ->: tr = (eval_gates wr rs xs).`1 by smt().
        move => H7 H8 H9; rewrite -H7 -H8.
        by rewrite -H1 -H2 /input /rand /trace /= /#.

      * move => w wl wr; progress.
        have H3: exists tl vwl, (tl,vwl) = eval_gates wl rs xs by exists (eval_gates wl rs xs).`1 (eval_gates wl rs xs).`2 => /#.
        elim H3 => tl vwl H3; rewrite -H3.
        have H4 : exists tr vwr, (tr,vwr) = eval_gates wr rs xs by exists (eval_gates wr rs xs).`1 (eval_gates wr rs xs).`2 => /#.
        elim H4 => tr vwr H4; rewrite -H4 /=.
        move : (MultiplicationGate.Gate.messages_consistency i j (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set) (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) w)))) pid_set)).
        rewrite /pid_set /gate /= H H0 /= /input /rand /trace
                !map_assoc //=.
        have : exists (tr0, ys), (tr0, ys) = eval (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) w)))) pid_set) (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set) 
          by exists (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) w)))) pid_set) (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).`1
                    (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) w)))) pid_set) (map (fun (pid : pid_t) => (pid, (tt, (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set)).`2 => /#.
        progress; move : H6; rewrite -H5 /=.
        rewrite !map_assoc //= /out_messages /get_messages_to /get_messages_from.
        move : (local_output_correct_gates witness wl i xs rs); rewrite H /=.
        move : (local_output_correct_gates witness wr i xs rs); rewrite H /=.
        have ->: tl = (eval_gates wl rs xs).`1 by smt().
        have ->: tr = (eval_gates wr rs xs).`1 by smt().
        move => H7 H8 H9; rewrite -H7 -H8.
        by rewrite -H1 -H2 /input /rand /trace => /#.

      * move => w wl wr; progress.
        have H3: exists tl vwl, (tl,vwl) = eval_gates wl rs xs by exists (eval_gates wl rs xs).`1 (eval_gates wl rs xs).`2 => /#.
        elim H3 => tl vwl H3; rewrite -H3.
        have H4 : exists tr vwr, (tr,vwr) = eval_gates wr rs xs by exists (eval_gates wr rs xs).`1 (eval_gates wr rs xs).`2 => /#.
        elim H4 => tr vwr H4; rewrite -H4 /=.
        move : (SMultiplicationGate.Gate.messages_consistency i j (map (fun (pid : pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set) (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) w)))) pid_set)).
        rewrite /pid_set /gate /= H H0 /= /input /rand /trace
                !map_assoc //=.
        have : exists (tr0, ys), (tr0, ys) = eval (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) w)))) pid_set) (map (fun (pid : pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set) 
          by exists (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) w)))) pid_set) (map (fun (pid : pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)).`1
                    (eval (map (fun (pid : pid_t) => (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) w)))) pid_set) (map (fun (pid : pid_t) => (pid, (oget (assoc vwl pid), (oget (assoc vwr pid))))) pid_set)).`2 => /#.
        progress; move : H6; rewrite -H5 /=.
        rewrite !map_assoc //= /out_messages /get_messages_to /get_messages_from.
        move : (local_output_correct_gates witness wl i xs rs); rewrite H /=.
        move : (local_output_correct_gates witness wr i xs rs); rewrite H /=.
        have ->: tl = (eval_gates wl rs xs).`1 by smt().
        have ->: tr = (eval_gates wr rs xs).`1 by smt().
        move => H7 H8 H9; rewrite -H7 -H8.
        by rewrite -H1 -H2 /input /rand /trace => /#.
  qed.

  lemma messages_consistency_aux (c : circuit_t) (i j : pid_t) (xs : inputs_t) (rs : rands_t) :
    i \in pid_set => j \in pid_set =>
    let (tr, y) = protocol c rs xs in
    get_messages_to j (out_messages c i (input i xs, rand i rs, trace i tr)) = 
    get_messages_from i (trace j tr).`2.
  proof.
    rewrite /get_messages_to /get_messages_from /= /out_messages /= /trace /=.
    elim c => topo gg /=; progress.
    move : x1 x2 H1 => trs ys; progress.
    have ->: valid_circuit_trace (topo, gg) (oget (assoc trs i)).`2 by
      move : (valid_trace_protocol (topo, gg) rs xs i);
        rewrite H H1 /= /valid_circuit_trace /trace /= /#.
    simplify.
    move : (messages_gates_consistency gg i j xs rs).
    rewrite H H0 /=; progress.
    have ->: trs = (protocol (topo, gg) rs xs).`1 by smt().
    rewrite /protocol /=; move : H1.
    elim topo => np ns m q /=; progress.
    have H5 : exists (tr', y'), (tr', y') = eval_gates gg rs xs
      by exists (eval_gates gg rs xs).`1 (eval_gates gg rs xs).`2 => /#.
    rewrite /eval_circuit /=.
    elim H5 => tr' y' /= H5; rewrite -H5; progress.
    by rewrite !map_assoc //= !map_assoc //= => /#. 
  qed.

  op consistent_views (c : circuit_t) (vi vj : view_t) (i j : pid_t) : bool =
    let (xi, ri, ti) = vi in
    let (xj, rj, tj) = vj in
    get_messages_to j (out_messages c i (xi, ri, ti)) = 
    get_messages_from i (tj).`2.

  lemma messages_consistency (c : circuit_t) (i j : pid_t) (xs : inputs_t) (rs : rands_t) :
    i \in pid_set => j \in pid_set =>
    valid_rands c rs =>
    valid_circuit c =>
    valid_inputs c xs =>
    let (tr, y) = protocol c rs xs in
    let vi = (input i xs,rand i rs,(trace i tr)) in
    let vj = (input j xs,rand j rs,(trace j tr)) in
    consistent_views c vi vj i j.
  proof.
    progress; rewrite /consistent_views.
    move : x1 x2 H4; move => tr ys H4.
    move : (messages_consistency_aux c i j xs rs).
    by rewrite H H0 /= H4 /=.
  qed.

  clone import Protocol as ArithP with 
    (*type ProtocolFunctionality.Circuit.Domain.wire_t = ArithmeticProtocolFunctionality.ArithmeticCircuit.Circuit.Domain.wire_t,
    op ProtocolFunctionality.Circuit.Domain.wire_to_bool = ArithmeticProtocolFunctionality.ArithmeticCircuit.Circuit.Domain.wire_to_bool,

    type ProtocolFunctionality.Circuit.gates_t = ArithmeticProtocolFunctionality.ArithmeticCircuit.Circuit.gates_t,
    op ProtocolFunctionality.Circuit.valid_gates = ArithmeticProtocolFunctionality.ArithmeticCircuit.Circuit.valid_gates,*)
    type ProtocolFunctionality.circuit_t = ArithmeticProtocolFunctionality.ArithmeticCircuit.Circuit.circuit_t,
    op ProtocolFunctionality.valid_circuit = ArithmeticProtocolFunctionality.ArithmeticCircuit.Circuit.valid_circuit,

    op ProtocolFunctionality.n = ArithmeticProtocolFunctionality.ProtocolFunctionality.n,
    op ProtocolFunctionality.t = ArithmeticProtocolFunctionality.ProtocolFunctionality.t,
    type ProtocolFunctionality.pid_t = ArithmeticProtocolFunctionality.ProtocolFunctionality.pid_t,
    op ProtocolFunctionality.pid_set = ArithmeticProtocolFunctionality.ProtocolFunctionality.pid_set,
    type ProtocolFunctionality.pinput_t = ArithmeticProtocolFunctionality.ProtocolFunctionality.pinput_t,
    type ProtocolFunctionality.sinput_t = ArithmeticProtocolFunctionality.ProtocolFunctionality.sinput_t,
    op ProtocolFunctionality.valid_inputs = ArithmeticProtocolFunctionality.ProtocolFunctionality.valid_inputs,
    type ProtocolFunctionality.output_t = ArithmeticProtocolFunctionality.ProtocolFunctionality.output_t,
    op ProtocolFunctionality.f = ArithmeticProtocolFunctionality.ProtocolFunctionality.f,

    type rand_t = rand_t,
    op valid_rand = valid_rand,

    (*type msgs_t = msgs_t,*)
    type in_messages_t = in_messages_t,
    (*type out_messages_t = out_messages_t,*)
    (*op get_messages_from = get_messages_from,*)
    (*op get_messages_to = get_messages_to,*)

    type poutput_t = share_t,

    (*op valid_circuit_trace = valid_circuit_trace,*)
    
    (*op out_messages = out_messages,*)
    op local_output = local_output,
    op protocol = protocol,
    op consistent_views = consistent_views
  proof ProtocolFunctionality.n_pos, ProtocolFunctionality.t_pos,
        ProtocolFunctionality.pid_set_uniq, ProtocolFunctionality.pid_set_size,
        correct, local_output_correct, messages_consistency, correct_domain.
  realize ProtocolFunctionality.n_pos by apply n_pos.
  realize ProtocolFunctionality.t_pos by apply t_pos.
  realize ProtocolFunctionality.pid_set_uniq by apply pid_set_uniq.
  realize ProtocolFunctionality.pid_set_size by apply pid_set_size.
  realize correct.
    progress; move : (correct c rs xs). 
    move : H H0.
    rewrite /valid_inputs /= /valid_rands /= /valid_rand /= /pid_set /ProtocolFunctionality.valid_circuit => -> [->] H /=. 
    have ->: (forall (pid : pid_t), pid \in pid_set => let (_, gg) = c in gates_valid_rand gg (oget (assoc rs pid))) <=> true by smt().
    move : H H1. elim c => topo gg; progress.
    move : H2. rewrite H H0 /=.
    move : H1. rewrite /valid_rands /=; progress.
    move : H3; rewrite H1 /pid_set /=.
    by smt().
  qed.
  realize local_output_correct by apply local_output_correct.
  realize messages_consistency by apply messages_consistency.
  realize correct_domain.
move => c rs xs. 
rewrite /protocol /=.
    elim c => topo gg.
    elim topo => n m q /=.
rewrite /eval_circuit.

    have : exists (tr', ys), (tr', ys) = eval_gates gg rs xs
      by exists (eval_gates gg rs xs).`1 (eval_gates gg rs xs).`2 => /#.    
    progress.
rewrite -H /=.
by rewrite -map_comp /(\o) /= map_id.
rewrite -H /=.
by rewrite -map_comp /(\o) /= map_id.
  qed.

end ArithmeticProtocol.
