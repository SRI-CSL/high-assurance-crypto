require import Distr.

from General require import ECList Utils.
from Circuit require import ArithmeticCircuit.
from Functionalities require import ArithmeticProtocolFunctionality.
from SecretSharing require import Shamir.
from BGW require import BGW.
from CommitmentScheme require import CRPRFCommitment.
from MPCInTheHead require import InTheHeadSigmaProtocol.

import ArithmeticCircuit Shamir BGW CRPRFCommitment ArithmeticProtocolFunctionality.

theory ShamirBGWCRPRFCSInTheHead.

  clone import InTheHead with
    theory SS <- Shamir.SecretSharingScheme,
    theory MPC <- BGW.WeakPrivacyComposition.PP,
    theory CS <- CRPRFCommitment.CS.

end ShamirBGWCRPRFCSInTheHead.
