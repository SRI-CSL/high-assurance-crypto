open Shamir
open BGWAddition
open BGWMultiplication
open BGWSMultiplication

open BGWGate
open BGWRefresh

open WeakPrivacyComposition

module BGW (PC : PartyConfiguration) = WeakPrivate (ShamirData (PC)) (BGWAdditionData (PC)) (BGWMultiplicationData (PC)) (BGWSMultiplicationData (PC)) (BGWRefreshGateData (PC))
