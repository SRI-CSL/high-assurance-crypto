require import AllCore List.

from MPC require import WeakPrivacyComposition.
from BGW require import BGWGate Refresh.

theory BGW.

clone import BGWGate.
import BGWRefresh.

clone import WeakPrivacyComposition with 
theory ArithmeticProtocol.SecretSharingScheme <- BGWGate.BGWMultiplication.HMShamir.SecretSharingScheme,
theory ArithmeticProtocol.AdditionGate <- BGWGate.BGWAddition.AdditionGate,
theory ArithmeticProtocol.MultiplicationGate <- BGWGate.BGWMultiplication.MultiplicationGate,
theory ArithmeticProtocol.SMultiplicationGate <- BGWGate.BGWSMultiplication.SMultiplicationGate,

theory SG <- RefreshGate.

end BGW.
