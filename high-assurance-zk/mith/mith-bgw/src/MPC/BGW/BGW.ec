require import AllCore List.

from MPC require import WeakPrivacyComposition.
from BGW require import BGWGate Refresh.

theory BGW.

clone import BGWGate.

clone import BGWRefresh with 
  op n = BGWGate.ArithmeticProtocol.SecretSharingScheme.n,
  op t = BGWGate.ArithmeticProtocol.SecretSharingScheme.t,

  op HMShamir.pid_set = BGWGate.ArithmeticProtocol.SecretSharingScheme.pid_set.

clone import WeakPrivacyComposition with 
theory ArithmeticProtocol.SecretSharingScheme = BGWGate.BGWMultiplication.HMShamir.SecretSharingScheme,
theory ArithmeticProtocol.AdditionGate = BGWGate.BGWAddition.AdditionGate,
theory ArithmeticProtocol.MultiplicationGate = BGWGate.BGWMultiplication.MultiplicationGate,
theory ArithmeticProtocol.SMultiplicationGate = BGWGate.BGWSMultiplication.SMultiplicationGate,
theory ArithmeticProtocol.InputGate = BGWGate.BGWInput.InputGate,

theory SG = BGWRefresh.RefreshGate.

end BGW.
