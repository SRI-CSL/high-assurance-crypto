module ZK = struct
  module LPZK = LPZK
end

module MPC = struct
  module AGate = AGate
  module AMPCProtocol = AMPCProtocol
  module AdditionGate = AdditionGate
  module MultiplicationGate = MultiplicationGate
  module SMultiplicationGate = SMultiplicationGate
  module ArithmeticProtocol = ArithmeticProtocol
  module WeakPrivacyComposition = WeakPrivacyComposition
  module BGW = BGW
end

module Commitment = struct
  module ACommitment = ACommitment
  module CRPRFCommitment = CRPRFCommitment
  module SHA3Commitment = SHA3Commitment
end

module SecretSharing = struct
  module ASecretSharing = ASecretSharing
  module Shamir = Shamir
end

module Random = Random

module EcLib = struct
  module EcCore = EcCore
  module EcList = EcList
  module EcOption = EcOption
  module EcPrimeField = EcPrimeField
end

module Circuit = struct
  module ACircuit = ACircuit
  module ArithmeticCircuit = ArithmeticCircuit
end 

module Zarith = struct
  module FieldPolynomial = FieldPolynomial
end