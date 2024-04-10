open Shamir
open BGWAddition
open BGWMultiplication
open BGWSMultiplication

open ArithmeticProtocol

module BGWWeak (PC: PartyConfiguration) = ArithmeticProtocol (ShamirData (PC)) (BGWAdditionData (PC)) (BGWMultiplicationData (PC)) (BGWSMultiplicationData (PC))
