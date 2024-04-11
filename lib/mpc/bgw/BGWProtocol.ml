open Shamir
open BGWAddition
open BGWMultiplication
open BGWSMultiplication

open BGWWeak
open BGWRefresh

open WeakPrivacyComposition

module BGWProtocol (PC : PartyConfiguration) = WeakPrivate (ShamirData (PC)) (BGWAdditionData (PC)) (BGWMultiplicationData (PC)) (BGWSMultiplicationData (PC)) (BGWRefreshGateData (PC))