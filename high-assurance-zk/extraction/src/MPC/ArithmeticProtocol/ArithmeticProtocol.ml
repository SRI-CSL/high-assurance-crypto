open Utils
open ECList
open Option
open Core
open PrimeField
   
open FieldPolynomial

open AProtocol
   
open ArithmeticCircuit
open ArithmeticDomain

open AdditionGate
open MultiplicationGate
open SMultiplicationGate
open ConstantGate

open ASecretSharingScheme
   
module ArithmeticProtocolData
         (SSD : sig include SecretSharingSchemeData with type secret_t = t and type share_t = t end)
         (AGED : sig include AdditionGateEvalData with type pid_t = SSD.pid_t and
                                                       type pinput_t = unit and
                                                       type sinput_t = SSD.share_t and
                                                       type output_t = SSD.secret_t and
                                                       type poutput_t = SSD.share_t end)
         (MGED : sig include MultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                             type pinput_t = unit and
                                                             type sinput_t = SSD.share_t and
                                                             type output_t = SSD.secret_t and
                                                             type poutput_t = SSD.share_t end)
         (SMGED : sig include SMultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                              type pinput_t = SSD.share_t and
                                                              type sinput_t = SSD.share_t and
                                                              type output_t = SSD.secret_t and
                                                              type poutput_t = SSD.share_t end) = struct

  

  module SS = SecretSharingScheme(SSD)
  module AdditionGate = AdditionGate (SSD) (AGED)
  module MultiplicationGate = MultiplicationGate (SSD) (MGED)
  module SMultiplicationGate = SMultiplicationGate (SSD) (SMGED)

  open ArithmeticCircuit
     
  type circuit_t = ArithmeticCircuit.circuit_t

  let n : Z.t = SSD.n
  let t : Z.t = SSD.t

  type pid_t = SSD.pid_t
  let pid_set : pid_t list = SSD.pid_set

  type pinput_t = SSD.secret_t list
  type sinput_t = SSD.share_t list
  type input_t = pinput_t * sinput_t
  type inputs_t = (pid_t * input_t) list

  let input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid)
  let pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (oget (assoc xs pid))
  let sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (oget (assoc xs pid))

  type output_t = SSD.secret_t
  type outputs_t = (pid_t * output_t) list

  type gate_rand_t =
    | AdditionRand of AdditionGate.rand_t
    | MultiplicationRand of MultiplicationGate.rand_t
    | SMultiplicationRand of SMultiplicationGate.rand_t
    | BadRand
 
  let is_gate_rand_addition (r : gate_rand_t) : bool =
    match r with
    | AdditionRand ra -> true
    | MultiplicationRand rm -> false
    | SMultiplicationRand rsm -> false
    | BadRand -> false
               
  let as_gate_rand_addition (r : gate_rand_t) =
    match r with
    | AdditionRand ra -> ra
    | MultiplicationRand rm -> witness
    | SMultiplicationRand rsm -> witness
    | BadRand -> witness

  let is_gate_rand_multiplication (r : gate_rand_t) : bool =
    match r with
    | AdditionRand ra -> false
    | MultiplicationRand rm -> true
    | SMultiplicationRand rsm -> false
    | BadRand -> false
               
  let as_gate_rand_multiplication (r : gate_rand_t) =
    match r with
    | AdditionRand ra -> witness
    | MultiplicationRand rm -> rm
    | SMultiplicationRand rsm -> witness
    | BadRand -> witness

  let is_gate_rand_smultiplication (r : gate_rand_t) : bool =
    match r with
    | AdditionRand ra -> false
    | MultiplicationRand rm -> false
    | SMultiplicationRand rsm -> true
    | BadRand -> false
               
  let as_gate_rand_smultiplication (r : gate_rand_t) =
    match r with
    | AdditionRand ra -> witness
    | MultiplicationRand rm -> witness
    | SMultiplicationRand rsm -> rsm
    | BadRand -> witness
               
  type rand_t = (gid_t * gate_rand_t) list
                        
  type rands_t = (pid_t * rand_t) list
  let rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid)

  type gate_traces_t =
    | PInputT of t
    | SInputT of wid_t
    | ConstantT of gid_t * t
    | AdditionT of gid_t * (pid_t * ((pid_t * AdditionGate.msgs_t) list)) list * gate_traces_t * gate_traces_t
    | MultiplicationT of gid_t * (pid_t * ((pid_t * MultiplicationGate.msgs_t) list)) list * gate_traces_t * gate_traces_t
    | SMultiplicationT of gid_t * (pid_t * ((pid_t * SMultiplicationGate.msgs_t) list)) list * gate_traces_t * gate_traces_t
  
  let is_gate_traces_pinput (lt : gate_traces_t) : bool =
    match lt with
    | PInputT w -> true
    | SInputT w -> false
    | ConstantT (gid, c) -> false
    | AdditionT (gid, tr, trl, trr) -> false
    | MultiplicationT (gid, tr, trl, trr) -> false
    | SMultiplicationT (gid, tr, trl, trr) -> false
    
  let as_gate_traces_pinput (lt : gate_traces_t) =
    match lt with
    | PInputT w -> w
    | SInputT w -> witness
    | ConstantT (gid, c) -> witness
    | AdditionT (gid, tr, trl, trr) -> witness
    | MultiplicationT (gid, tr, trl, trr) -> witness
    | SMultiplicationT (gid, tr, trl, trr) -> witness
    
  let is_gate_traces_sinput (lt : gate_traces_t) : bool =
    match lt with
    | PInputT w -> false
    | SInputT w -> true
    | ConstantT (gid, c) -> false
    | AdditionT (gid, tr, trl, trr) -> false
    | MultiplicationT (gid, tr, trl, trr) -> false
    | SMultiplicationT (gid, tr, trl, trr) -> false
    
  let as_gate_traces_sinput (lt : gate_traces_t) : wid_t =
    match lt with
    | PInputT w -> witness
    | SInputT w -> w
    | ConstantT (gid, c) -> witness
    | AdditionT (gid, tr, trl, trr) -> witness
    | MultiplicationT (gid, tr, trl, trr) -> witness
    | SMultiplicationT (gid, tr, trl, trr) -> witness
    
  let is_gate_traces_constant (lt : gate_traces_t) : bool =
    match lt with
    | PInputT w -> false
    | SInputT w -> false
    | ConstantT (gid, c) -> true
    | AdditionT (gid, tr, trl, trr) -> false
    | MultiplicationT (gid, tr, trl, trr) -> false
    | SMultiplicationT (gid, tr, trl, trr) -> false
    
  let as_gate_traces_constant (lt : gate_traces_t) =
    match lt with    
    | PInputT w -> witness
    | SInputT w -> witness
    | ConstantT (gid, c) -> [c]
    | AdditionT (gid, tr, trl, trr) -> witness
    | MultiplicationT (gid, tr, trl, trr) -> witness
    | SMultiplicationT (gid, tr, trl, trr) -> witness
    
  let is_gate_traces_addition (lt : gate_traces_t) : bool =
    match lt with
    | PInputT w -> false
    | SInputT w -> false
    | ConstantT (gid, c) -> false
    | AdditionT (gid, tr, trl, trr) -> true
    | MultiplicationT (gid, tr, trl, trr) -> false
    | SMultiplicationT (gid, tr, trl, trr) -> false
    
  let as_gate_traces_addition (lt : gate_traces_t) =
    match lt with
    | PInputT w -> witness
    | SInputT w -> witness
    | ConstantT (gid, c) -> witness
    | AdditionT (gid, tr, trl, trr) -> (gid,tr,trl,trr)
    | MultiplicationT (gid, tr, trl, trr) -> witness
    | SMultiplicationT (gid, tr, trl, trr) -> witness
    
  let is_gate_traces_multiplication (lt : gate_traces_t) : bool =
    match lt with
    | PInputT w -> false
    | SInputT w -> false
    | ConstantT (gid, c) -> false
    | AdditionT (gid, tr, trl, trr) -> false
    | MultiplicationT (gid, tr, trl, trr) -> true
    | SMultiplicationT (gid, tr, trl, trr) -> false
    
  let as_gate_traces_multiplication (lt : gate_traces_t) =
    match lt with
    | PInputT w -> witness
    | SInputT w -> witness
    | ConstantT (gid, c) -> witness
    | AdditionT (gid, tr, trl, trr) -> witness
    | MultiplicationT (gid, tr, trl, trr) -> (gid,tr,trl,trr)
    | SMultiplicationT (gid, tr, trl, trr) -> witness
    
  let is_gate_traces_smultiplication (lt : gate_traces_t) : bool =
    match lt with    
    | PInputT w -> false
    | SInputT w -> false
    | ConstantT (gid, c) -> false
    | AdditionT (gid, tr, trl, trr) -> false
    | MultiplicationT (gid, tr, trl, trr) -> false
    | SMultiplicationT (gid, tr, trl, trr) -> true
    
  let as_gate_traces_smultiplication (lt : gate_traces_t) =
    match lt with    
    | PInputT w -> witness
    | SInputT w -> witness
    | ConstantT (gid, c) -> witness
    | AdditionT (gid, tr, trl, trr) -> witness
    | MultiplicationT (gid, tr, trl, trr) -> witness
    | SMultiplicationT (gid, tr, trl, trr) -> (gid,tr,trl,trr)

  type gate_local_traces_t =
    | PInputLT of t
    | SInputLT of wid_t
    | ConstantLT of gid_t * t
    | AdditionLT of gid_t * (pid_t * AdditionGate.msgs_t) list * gate_local_traces_t * gate_local_traces_t
    | MultiplicationLT of gid_t * (pid_t * MultiplicationGate.msgs_t) list * gate_local_traces_t * gate_local_traces_t
    | SMultiplicationLT of gid_t * (pid_t * SMultiplicationGate.msgs_t) list * gate_local_traces_t * gate_local_traces_t
  
  let is_gate_local_traces_pinput (lt : gate_local_traces_t) : bool =
    match lt with    
    | PInputLT w -> true
    | SInputLT w -> false
    | ConstantLT (gid, c) -> false
    | AdditionLT (gid, tr, trl, trr) -> false
    | MultiplicationLT (gid, tr, trl, trr) -> false
    | SMultiplicationLT (gid, tr, trl, trr) -> false
    
  let as_gate_local_traces_pinput (lt : gate_local_traces_t) =
    match lt with    
    | PInputLT w -> w
    | SInputLT w -> witness
    | ConstantLT (gid, c) -> witness
    | AdditionLT (gid, tr, trl, trr) -> witness
    | MultiplicationLT (gid, tr, trl, trr) -> witness
    | SMultiplicationLT (gid, tr, trl, trr) -> witness
    
  let is_gate_local_traces_sinput (lt : gate_local_traces_t) : bool =
    match lt with        
    | PInputLT w -> false
    | SInputLT w -> true
    | ConstantLT (gid, c) -> false
    | AdditionLT (gid, tr, trl, trr) -> false
    | MultiplicationLT (gid, tr, trl, trr) -> false
    | SMultiplicationLT (gid, tr, trl, trr) -> false
    
  let as_gate_local_traces_sinput (lt : gate_local_traces_t) : wid_t =
    match lt with    
    | PInputLT w -> witness
    | SInputLT w -> w
    | ConstantLT (gid, c) -> witness
    | AdditionLT (gid, tr, trl, trr) -> witness
    | MultiplicationLT (gid, tr, trl, trr) -> witness
    | SMultiplicationLT (gid, tr, trl, trr) -> witness
    
  let is_gate_local_traces_constant (lt : gate_local_traces_t) : bool =
    match lt with    
    | PInputLT w -> false
    | SInputLT w -> false
    | ConstantLT (gid, c) -> true
    | AdditionLT (gid, tr, trl, trr) -> false
    | MultiplicationLT (gid, tr, trl, trr) -> false
    | SMultiplicationLT (gid, tr, trl, trr) -> false
    
  let as_gate_local_traces_constant (lt : gate_local_traces_t) =
    match lt with    
    | PInputLT w -> witness
    | SInputLT w -> witness
    | ConstantLT (gid, c) -> [c]
    | AdditionLT (gid, tr, trl, trr) -> witness
    | MultiplicationLT (gid, tr, trl, trr) -> witness
    | SMultiplicationLT (gid, tr, trl, trr) -> witness
    
  let is_gate_local_traces_addition (lt : gate_local_traces_t) : bool =
    match lt with    
    | PInputLT w -> false
    | SInputLT w -> false
    | ConstantLT (gid, c) -> false
    | AdditionLT (gid, tr, trl, trr) -> true
    | MultiplicationLT (gid, tr, trl, trr) -> false
    | SMultiplicationLT (gid, tr, trl, trr) -> false
    
  let as_gate_local_traces_addition (lt : gate_local_traces_t) =
    match lt with    
    | PInputLT w -> witness
    | SInputLT w -> witness
    | ConstantLT (gid, c) -> witness
    | AdditionLT (gid, tr, trl, trr) -> (gid,tr,trl,trr)
    | MultiplicationLT (gid, tr, trl, trr) -> witness
    | SMultiplicationLT (gid, tr, trl, trr) -> witness
    
  let is_gate_local_traces_multiplication (lt : gate_local_traces_t) : bool =
    match lt with    
    | PInputLT w -> false
    | SInputLT w -> false
    | ConstantLT (gid, c) -> false
    | AdditionLT (gid, tr, trl, trr) -> false
    | MultiplicationLT (gid, tr, trl, trr) -> true
    | SMultiplicationLT (gid, tr, trl, trr) -> false
    
  let as_gate_local_traces_multiplication (lt : gate_local_traces_t) =
    match lt with    
    | PInputLT w -> witness
    | SInputLT w -> witness
    | ConstantLT (gid, c) -> witness
    | AdditionLT (gid, tr, trl, trr) -> witness
    | MultiplicationLT (gid, tr, trl, trr) -> (gid,tr,trl,trr)
    | SMultiplicationLT (gid, tr, trl, trr) -> witness
    
  let is_gate_local_traces_smultiplication (lt : gate_local_traces_t) : bool =
    match lt with    
    | PInputLT w -> false
    | SInputLT w -> false
    | ConstantLT (gid, c) -> false
    | AdditionLT (gid, tr, trl, trr) -> false
    | MultiplicationLT (gid, tr, trl, trr) -> false
    | SMultiplicationLT (gid, tr, trl, trr) -> true
    
  let as_gate_local_traces_smultiplication (lt : gate_local_traces_t) =
    match lt with    
    | PInputLT w -> witness
    | SInputLT w -> witness
    | ConstantLT (gid, c) -> witness
    | AdditionLT (gid, tr, trl, trr) -> witness
    | MultiplicationLT (gid, tr, trl, trr) -> witness
    | SMultiplicationLT (gid, tr, trl, trr) -> (gid,tr,trl,trr)

  let rec get_local_trace (pid : pid_t) (gt : gate_traces_t) : gate_local_traces_t =
    match gt with
    | PInputT w -> PInputLT w
    | SInputT w -> SInputLT w
    | ConstantT (gid, c) -> ConstantLT (gid, c)
    | AdditionT (gid, tr, trl, trr) -> AdditionLT (gid, (oget (assoc tr pid)), (get_local_trace pid trl), (get_local_trace pid trr))
    | MultiplicationT (gid, tr, trl, trr) -> MultiplicationLT (gid, (oget (assoc tr pid)), (get_local_trace pid trl), (get_local_trace pid trr))
    | SMultiplicationT (gid, tr, trl, trr) -> SMultiplicationLT (gid, (oget (assoc tr pid)), (get_local_trace pid trl), (get_local_trace pid trr))

  type gate_local_msgs_t =
    | PInputLM of t
    | SInputLM of wid_t
    | ConstantLM of gid_t * t
    | AdditionLM of gid_t * AdditionGate.msgs_t * gate_local_msgs_t * gate_local_msgs_t
    | MultiplicationLM of gid_t * MultiplicationGate.msgs_t * gate_local_msgs_t * gate_local_msgs_t
    | SMultiplicationLM of gid_t * SMultiplicationGate.msgs_t * gate_local_msgs_t * gate_local_msgs_t
 
  let is_gate_local_msgs_pinput (lt : gate_local_msgs_t) : bool =
    match lt with
    | PInputLM w -> true
    | SInputLM w -> false
    | ConstantLM (gid, c) -> false
    | AdditionLM (gid, tr, trl, trr) -> false
    | MultiplicationLM (gid, tr, trl, trr) -> false
    | SMultiplicationLM (gid, tr, trl, trr) -> false
    
  let as_gate_local_msgs_pinput (lt : gate_local_msgs_t) =
    match lt with
    | PInputLM w -> w
    | SInputLM w -> witness
    | ConstantLM (gid, c) -> witness
    | AdditionLM (gid, tr, trl, trr) -> witness
    | MultiplicationLM (gid, tr, trl, trr) -> witness
    | SMultiplicationLM (gid, tr, trl, trr) -> witness
    
  let is_gate_local_msgs_sinput (lt : gate_local_msgs_t) : bool =
    match lt with
    | PInputLM w -> false
    | SInputLM w -> true
    | ConstantLM (gid, c) -> false
    | AdditionLM (gid, tr, trl, trr) -> false
    | MultiplicationLM (gid, tr, trl, trr) -> false
    | SMultiplicationLM (gid, tr, trl, trr) -> false
    
  let as_gate_local_msgs_sinput (lt : gate_local_msgs_t) : wid_t =
    match lt with
    | PInputLM w -> witness
    | SInputLM w -> w
    | ConstantLM (gid, c) -> witness
    | AdditionLM (gid, tr, trl, trr) -> witness
    | MultiplicationLM (gid, tr, trl, trr) -> witness
    | SMultiplicationLM (gid, tr, trl, trr) -> witness
    
  let is_gate_local_msgs_constant (lt : gate_local_msgs_t) : bool =
    match lt with
    | PInputLM w -> false
    | SInputLM w -> false
    | ConstantLM (gid, c) -> true
    | AdditionLM (gid, tr, trl, trr) -> false
    | MultiplicationLM (gid, tr, trl, trr) -> false
    | SMultiplicationLM (gid, tr, trl, trr) -> false
    
  let as_gate_local_msgs_constant (lt : gate_local_msgs_t) =
    match lt with
    | PInputLM w -> witness
    | SInputLM w -> witness
    | ConstantLM (gid, c) -> [c]
    | AdditionLM (gid, tr, trl, trr) -> witness
    | MultiplicationLM (gid, tr, trl, trr) -> witness
    | SMultiplicationLM (gid, tr, trl, trr) -> witness
    
  let is_gate_local_msgs_addition (lt : gate_local_msgs_t) : bool =
    match lt with
    | PInputLM w -> false
    | SInputLM w -> false
    | ConstantLM (gid, c) -> false
    | AdditionLM (gid, tr, trl, trr) -> true
    | MultiplicationLM (gid, tr, trl, trr) -> false
    | SMultiplicationLM (gid, tr, trl, trr) -> false
    
  let as_gate_local_msgs_addition (lt : gate_local_msgs_t) =
    match lt with
    | PInputLM w -> witness
    | SInputLM w -> witness
    | ConstantLM (gid, c) -> witness
    | AdditionLM (gid, tr, trl, trr) -> (gid,tr,trl,trr)
    | MultiplicationLM (gid, tr, trl, trr) -> witness
    | SMultiplicationLM (gid, tr, trl, trr) -> witness
    
  let is_gate_local_msgs_multiplication (lt : gate_local_msgs_t) : bool =
    match lt with
    | PInputLM w -> false
    | SInputLM w -> false
    | ConstantLM (gid, c) -> false
    | AdditionLM (gid, tr, trl, trr) -> false
    | MultiplicationLM (gid, tr, trl, trr) -> true
    | SMultiplicationLM (gid, tr, trl, trr) -> false
    
  let as_gate_local_msgs_multiplication (lt : gate_local_msgs_t) =
    match lt with
    | PInputLM w -> witness
    | SInputLM w -> witness
    | ConstantLM (gid, c) -> witness
    | AdditionLM (gid, tr, trl, trr) -> witness
    | MultiplicationLM (gid, tr, trl, trr) -> (gid,tr,trl,trr)
    | SMultiplicationLM (gid, tr, trl, trr) -> witness
    
  let is_gate_local_msgs_smultiplication (lt : gate_local_msgs_t) : bool =
    match lt with
    | PInputLM w -> false
    | SInputLM w -> false
    | ConstantLM (gid, c) -> false
    | AdditionLM (gid, tr, trl, trr) -> false
    | MultiplicationLM (gid, tr, trl, trr) -> false
    | SMultiplicationLM (gid, tr, trl, trr) -> true
    
  let as_gate_local_msgs_smultiplication (lt : gate_local_msgs_t) =
    match lt with
    | PInputLM w -> witness
    | SInputLM w -> witness
    | ConstantLM (gid, c) -> witness
    | AdditionLM (gid, tr, trl, trr) -> witness
    | MultiplicationLM (gid, tr, trl, trr) -> witness
    | SMultiplicationLM (gid, tr, trl, trr) -> (gid,tr,trl,trr)

  let rec get_local_msgs_from (pid : pid_t) (gt : gate_local_traces_t) : gate_local_msgs_t =
    match gt with
    | PInputLT w -> PInputLM w
    | SInputLT w -> SInputLM w
    | ConstantLT (gid, c) -> ConstantLM (gid, c)
    | AdditionLT (gid, tr, trl, trr) -> AdditionLM (gid, (oget (assoc tr pid)), (get_local_msgs_from pid trl), (get_local_msgs_from pid trr))
    | MultiplicationLT (gid, tr, trl, trr) -> MultiplicationLM (gid, (oget (assoc tr pid)), (get_local_msgs_from pid trl), (get_local_msgs_from pid trr))
    | SMultiplicationLT (gid, tr, trl, trr) -> SMultiplicationLM (gid, (oget (assoc tr pid)), (get_local_msgs_from pid trl), (get_local_msgs_from pid trr))

  let rec get_local_msgs_to (pid : pid_t) (gt : gate_local_traces_t) : gate_local_msgs_t =
    match gt with
    | PInputLT w -> PInputLM w
    | SInputLT w -> SInputLM w
    | ConstantLT (gid, c) -> ConstantLM (gid, c)
    | AdditionLT (gid, tr, trl, trr) -> AdditionLM (gid, (AdditionGate.get_messages_to pid tr), (get_local_msgs_to pid trl), (get_local_msgs_to pid trr))
    | MultiplicationLT (gid, tr, trl, trr) -> MultiplicationLM (gid, (MultiplicationGate.get_messages_to pid tr), (get_local_msgs_to pid trl), (get_local_msgs_to pid trr))
    | SMultiplicationLT (gid, tr, trl, trr) -> SMultiplicationLM (gid, (SMultiplicationGate.get_messages_to pid tr), (get_local_msgs_to pid trl), (get_local_msgs_to pid trr))

  type msgs_t = gate_local_msgs_t
                                                 
  type in_messages_t = gate_local_traces_t
  type out_messages_t = gate_local_traces_t

  let get_messages_from (pid : pid_t) (ims : in_messages_t) : msgs_t = get_local_msgs_from pid ims
  let get_messages_to (pid : pid_t) (oms : out_messages_t) : msgs_t = get_local_msgs_to pid oms

  type trace_t = SS.shares_t * in_messages_t
  type traces_t = (pid_t * trace_t) list
  let trace (pid : pid_t) (trs : traces_t) : trace_t = oget (assoc trs pid)

  type view_t = input_t * rand_t * trace_t
  type views_t = (pid_t * view_t) list
  let view (pid : pid_t) (vs : views_t) : view_t = oget (assoc vs pid)

  let empty_rand = map (fun pid -> (pid, ())) pid_set

  type poutput_t = SS.share_t
  type poutputs_t = (pid_t * poutput_t) list
  let poutput (pid : pid_t) (ys : poutputs_t) : poutput_t = oget (assoc ys pid)
                 
  let rec eval_gates (gg : gates_t) (rs : rands_t) (xs : inputs_t) : gate_traces_t * SS.shares_t =
    match gg with
    | PInput w -> 
      let gys = SS.public_encoding (nth witness (pinput (head witness pid_set) xs) w) in
      let tr = PInputT (nth witness (pinput (head witness pid_set) xs) w) in
      (tr, gys)
      
    | SInput w -> 
      let ys = map (fun pid -> let sec = nth witness (sinput pid xs) w in (pid, sec)) pid_set in
      let tr = SInputT w in

      (tr, ys)

    | Constant (gid, c) -> 
      let gys = SS.public_encoding c in
      let tr = ConstantT (gid, c) in

      (tr, gys)

    | Addition (gid, wl, wr) -> 
      let ra = map (fun pid -> (pid, as_gate_rand_addition (oget (assoc (oget (assoc rs pid)) gid)))) pid_set in
      let (tl, vwl) = eval_gates wl rs xs in
      let (tr, vwr) = eval_gates wr rs xs in

      let gxs = map (fun pid -> (pid, ((), (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set in

      let (gtr, gys) = AGED.eval ra gxs in
      let gtrs = AdditionT (gid, gtr, tl, tr) in

      (gtrs, gys)

    | Multiplication (gid, wl, wr) -> 
      let ra = map (fun pid -> (pid, as_gate_rand_multiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set in
      let (tl, vwl) = eval_gates wl rs xs in
      let (tr, vwr) = eval_gates wr rs xs in

      let gxs = map (fun pid -> (pid, ((), (oget (assoc vwl pid), oget (assoc vwr pid))))) pid_set in

      let (gtr, gys) = MGED.eval ra gxs in
      let gtrs = MultiplicationT (gid, gtr, tl, tr) in

      (gtrs, gys)

    | SMultiplication (gid, wl, wr) -> 
      let ra = map (fun pid -> (pid, as_gate_rand_smultiplication (oget (assoc (oget (assoc rs pid)) gid)))) pid_set in
      let (tl, vwl) = eval_gates wl rs xs in
      let (tr, vwr) = eval_gates wr rs xs in

      let gxs = map (fun pid -> (pid, (oget (assoc vwl pid), (oget (assoc vwr pid), witness)))) pid_set in

      let (gtr, gys) = SMGED.eval ra gxs in
      let gtrs = SMultiplicationT (gid, gtr, tl, tr) in

      (gtrs, gys)

  let eval_circuit (cc : gates_t) (r : rands_t) (x : inputs_t) : gate_traces_t * SS.shares_t = eval_gates cc r x
                   
  let protocol (c : circuit_t) (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let (np,ns,m,q) = fst c in
    let cc = snd c in
    let (tr', ys) = eval_circuit cc rs xs in

    let y = SS.reconstruct ys in
    let ys' = map (fun pid -> (pid, y)) pid_set in

    let tr = map (fun pid -> (pid, get_local_trace pid tr')) pid_set in
    let trs = map (fun pid -> (pid, (ys, oget (assoc tr pid)))) pid_set in

    (trs,ys')

  let rec local_output_gates (pid : pid_t) (x : input_t) (r : rand_t) (im : gate_local_traces_t) : SS.share_t =
    match im with
    | PInputLT c -> oget (assoc (SS.public_encoding c) pid)
    | SInputLT w -> nth witness (snd x) w
    | ConstantLT (gid, c) -> oget (assoc (SS.public_encoding c) pid)
    | AdditionLT (gid, tr, trl, trr) -> 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in
      let ra = as_gate_rand_addition (oget (assoc r gid)) in
      AGED.local_output_share pid ((),(vl,vr)) ra tr
    | MultiplicationLT (gid, tr, trl, trr) -> 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in
      let rm = as_gate_rand_multiplication (oget (assoc r gid)) in
      MGED.local_output_share pid ((),(vl,vr)) rm tr
    | SMultiplicationLT (gid, tr, trl, trr) -> 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in
      let rm = as_gate_rand_smultiplication (oget (assoc r gid)) in
      SMGED.local_output_share pid (vl,(vr,witness)) rm tr

  let rec valid_trace_gates (g : gates_t) (gtr : gate_local_traces_t) : bool =
    match g with
    | PInput w -> is_gate_local_traces_pinput gtr
    | SInput w -> is_gate_local_traces_sinput gtr
    | Constant (gid, c) -> is_gate_local_traces_constant gtr
    | Addition (gid, wl, wr) ->
      is_gate_local_traces_addition gtr &&
        let (gid', gtr', tl, tr) = as_gate_local_traces_addition gtr in
        valid_trace_gates wl tl && valid_trace_gates wr tr
    | Multiplication (gid, wl, wr) ->
      is_gate_local_traces_multiplication gtr &&
        let (gid', gtr', tl, tr) = as_gate_local_traces_multiplication gtr in
        valid_trace_gates wl tl && valid_trace_gates wr tr
    | SMultiplication (gid, wl, wr) ->
      is_gate_local_traces_smultiplication gtr &&
        let (gid', gtr', tl, tr) = as_gate_local_traces_smultiplication gtr in
        valid_trace_gates wl tl && valid_trace_gates wr tr

  let valid_circuit_trace (c : circuit_t) (ims : in_messages_t) : bool =
    let (topo, gg) = c in valid_trace_gates gg ims

  let local_output (c : circuit_t) (pid : pid_t) (v : view_t) : output_t =
    let (x,r,tr) = v in
    let (topo, gg) = c in 
    let (ys,ims) = tr in
    if valid_circuit_trace c ims && local_output_gates pid x r ims = oget (assoc ys pid) then
      SS.reconstruct ys
    else witness

  let rec out_messages_gates (pid : pid_t) (x : input_t) (r : rand_t) (im : gate_local_traces_t) : gate_local_traces_t =
    match im with
    | PInputLT w -> PInputLT w
    | SInputLT w ->SInputLT w
    | ConstantLT (gid, c) -> ConstantLT (gid, c)
    | AdditionLT (gid, tr, trl, trr) -> 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in

      let owl = out_messages_gates pid x r trl in
      let owr = out_messages_gates pid x r trr in

      let ra = as_gate_rand_addition (oget (assoc r gid)) in
      AdditionLT (gid, (AGED.out_messages_in_messages pid ((),(vl,vr)) ra tr), owl, owr)
      
    | MultiplicationLT (gid, tr, trl, trr) -> 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in

      let owl = out_messages_gates pid x r trl in
      let owr = out_messages_gates pid x r trr in

      let rm = as_gate_rand_multiplication (oget (assoc r gid)) in
      MultiplicationLT (gid, (MGED.out_messages_in_messages pid ((),(vl,vr)) rm tr), owl, owr)

    | SMultiplicationLT (gid, tr, trl, trr) -> 
      let vl = local_output_gates pid x r trl in
      let vr = local_output_gates pid x r trr in

      let owl = out_messages_gates pid x r trl in
      let owr = out_messages_gates pid x r trr in

      let rm = as_gate_rand_smultiplication (oget (assoc r gid)) in
      SMultiplicationLT (gid, (SMGED.out_messages_in_messages pid ((vl),(vr,witness)) rm tr), owl, owr)

  let out_messages (c : circuit_t) (pid : pid_t) (v : view_t) : out_messages_t =
    let (topo, gg) = c in 
    let (x,r,tr) = v in
    if valid_circuit_trace c (snd tr) then out_messages_gates pid x r (snd tr)
    else witness

  let valid_trace_gates (g : gates_t) (gtr : gate_local_traces_t) : bool =
    match g with
    | PInput w -> is_gate_local_traces_pinput gtr
    | SInput w -> is_gate_local_traces_sinput gtr
    | Constant (gid, c) -> is_gate_local_traces_constant gtr
    | Addition (gid, wl, wr) ->
      is_gate_local_traces_addition gtr &&
        let (gid', gtr', tl, tr) = as_gate_local_traces_addition gtr in
        valid_trace_gates wl tl && valid_trace_gates wr tr
    | Multiplication (gid, wl, wr) ->
      is_gate_local_traces_multiplication gtr &&
        let (gid', gtr', tl, tr) = as_gate_local_traces_multiplication gtr in
        valid_trace_gates wl tl && valid_trace_gates wr tr
    | SMultiplication (gid, wl, wr) ->
      is_gate_local_traces_smultiplication gtr &&
        let (gid', gtr', tl, tr) = as_gate_local_traces_smultiplication gtr in
        valid_trace_gates wl tl && valid_trace_gates wr tr

  let valid_circuit_trace (c : circuit_t) (ims : in_messages_t) : bool =
    let (topo, gg) = c in valid_trace_gates gg ims    

end

(*module ArithmeticProtocol
         (SSD : sig include SecretSharingSchemeData with type secret_t = t and type share_t = t end)
         (AGED : sig include AdditionGateEvalData with type pid_t = SSD.pid_t and
                                                       type pinput_t = unit and
                                                       type sinput_t = SSD.share_t and
                                                       type output_t = SSD.secret_t and
                                                       type poutput_t = SSD.share_t end)
         (MGED : sig include MultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                             type pinput_t = unit and
                                                             type sinput_t = SSD.share_t and
                                                             type output_t = SSD.secret_t and
                                                             type poutput_t = SSD.share_t end)
         (SMGED : sig include SMultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                               type pinput_t = SSD.share_t and
                                                               type sinput_t = SSD.share_t and
                                                               type output_t = SSD.secret_t and
                                                               type poutput_t = SSD.share_t end) = Protocol (ArithmeticProtocolData (SSD) (AGED) (MGED) (SMGED))*)
                                                                                                     
                                                                                                                                    (*
  let rec zs_to_string = function 
    | Nil -> ""
    | Cons (x,xs) -> Z.to_string (snd x) ^ zs_to_string xs

  let rec msgs_to_string = function
    | PInputLM w -> Z.to_string w
    | SInputLM w -> ""
    | ConstantLM (gid, c) -> Z.to_string c
    | AdditionLM (gid, tr, trl, trr) -> zs_to_string (fst tr) ^ msgs_to_string trl ^ msgs_to_string trr
    | MultiplicationLM (gid, tr, trl, trr) -> zs_to_string tr ^ msgs_to_string trl ^ msgs_to_string trr
    | SMultiplicationLM (gid, tr, trl, trr) -> zs_to_string tr ^ msgs_to_string trl ^ msgs_to_string trr

  let rec gate_local_trace_to_string = function
    | PInputLT w -> Z.to_string w
    | SInputLT w -> ""
    | ConstantLT (gid, c) -> Z.to_string c
    | AdditionLT (gid, m, wl, wr) -> msgs_to_string m ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr
    | MultiplicationLT (gid, m, wl, wr) -> msgs_to_string m ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr
    | SMultiplicationLT (gid, m, wl, wr) -> msgs_to_string m ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr

  let rec gate_local_traces_to_string = function
    | Nil -> ""
    | Cons (x,xs) -> gate_local_trace_to_string x ^ gate_local_traces_to_string xs

  let input_to_string (x : input_t) : string =
    let (xp,xs) = x in (String.concat "" (map Z.to_string xp)) ^ (String.concat "" (map Z.to_string xs))

  let rand_to_string (r : rand_t) : string = polynomial_to_string r

  let trace_to_string (tr : trace_t) : string =
    let (ys, ims) = tr in zs_to_string ys ^ gate_local_trace_to_string ims

  let view_to_string (v : view_t) : string =
    let (x,r,tr) = v in input_to_string x ^ rand_to_string r ^ trace_to_string tr
                                                                                                                                     *)
