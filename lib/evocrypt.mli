module ZK : sig
  module LPZK = LPZK
  module MitH = MitH
  module ShamirBGWSha3MitH = ShamirBGWSha3MitH
end

module MPC : sig
  module AGate = AGate
  module AMPCProtocol = AMPCProtocol
  module AdditionGate = AdditionGate
  module MultiplicationGate = MultiplicationGate
  module SMultiplicationGate = SMultiplicationGate
  module ArithmeticProtocol = ArithmeticProtocol
  module WeakPrivacyComposition = WeakPrivacyComposition
  module BGW : sig
    module BGWAddition = BGWAddition
    module BGWMultiplication = BGWMultiplication
    module BGWSMultiplication = BGWSMultiplication
    module BGWRefresh = BGWRefresh
    module BGWProtocol = BGWProtocol
  end
end

module Commitment : sig
  module ACommitment = ACommitment
  module CRPRFCommitment = CRPRFCommitment
  module SHA3Commitment = SHA3Commitment
end

module SecretSharing : sig
  module ASecretSharing = ASecretSharing
  module Shamir = Shamir
end

module Random = Random

module EcLib : sig
  module EcCore = EcCore
  module EcList = EcList
  module EcOption = EcOption
  module EcPrimeField = EcPrimeField
end

module Circuit : sig
  module ACircuit = ACircuit
  module ArithmeticCircuit = ArithmeticCircuit
end 

module Zarith : sig
  module FieldPolynomial = FieldPolynomial
end