from ZeroKnowledge require import Completeness.
from SigmaProtocol require import ASigmaProtocol.

theory CompletenessSigmaProtocol.

  clone import SigmaProtocol.

  clone import Completeness with
    theory ZKPProtocol <- SigmaProtocol.ZKPProtocol.

end CompletenessSigmaProtocol.
