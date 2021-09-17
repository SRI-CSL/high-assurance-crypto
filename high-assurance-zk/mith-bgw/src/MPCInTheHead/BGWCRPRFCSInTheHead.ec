require import List Distr.

from General require import ListExt Utils PrimeField.
from Circuit require import ArithmeticCircuit.
from SecretSharing require import ASecretSharingScheme Additive.
from BGW require import BGW.
from Commitment require import CRPRFCommitment.
from MPCInTheHead require import InTheHead.
from MPC require import AProtocol.

import BGW CRPRFCommitment.

theory BGWCRPRFCSInTheHead.

  clone import Additive as Add with 
    op n = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.n,
    op pid_set = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.pid_set.
  clone import ListSecretSharingScheme as LAdd with
    theory SS = Add.SecretSharingScheme.

  clone import Protocol as BGWBool with
    type ProtocolFunctionality.circuit_t = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.circuit_t,
    op ProtocolFunctionality.n = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.n,
    op ProtocolFunctionality.t = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.t,
    type ProtocolFunctionality.pid_t = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.pid_t,
    op ProtocolFunctionality.pid_set = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.pid_set,
    type ProtocolFunctionality.pinput_t = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.pinput_t,
    type ProtocolFunctionality.sinput_t = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.sinput_t,
    op ProtocolFunctionality.valid_circuit = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.valid_circuit,
    op ProtocolFunctionality.valid_inputs = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.valid_inputs,
    type ProtocolFunctionality.output_t = bool,
    op ProtocolFunctionality.f (c : circuit_t) (xs : inputs_t) = 
      let r = BGW.WeakPrivacyComposition.PP.ProtocolFunctionality.f c xs in
      map (fun pid => (pid, oget (assoc r pid) = fzero)) pid_set,

    type rand_t = BGW.WeakPrivacyComposition.PP.rand_t,
    op valid_rand = BGW.WeakPrivacyComposition.PP.valid_rand,
    type in_messages_t = BGW.WeakPrivacyComposition.PP.in_messages_t,
    type poutput_t = BGW.WeakPrivacyComposition.PP.poutput_t,

    op local_output c pid v =
      let r = BGW.WeakPrivacyComposition.PP.local_output c pid v in
      r = fzero,
    op protocol c r xs =
      let (tr, ys) = BGW.WeakPrivacyComposition.PP.protocol c r xs in
      (tr, map (fun pid => (pid, oget (assoc ys pid) = fzero)) LAdd.pid_set).

  clone import CRPRFCommitment with
    type input = view_t.

  clone import InTheHead with
    type witness_t = t list,
    type instance_t = t list,
    theory SS = LAdd,
    theory MPC = BGWBool,
    theory CS = CRPRFCommitment.CS.

end BGWCRPRFCSInTheHead.
