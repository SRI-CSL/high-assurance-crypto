
# FORMAL VERIFICATION OF A BGW BASED INSTANTIATION OF THE "MPC-IN-THE-HEAD" CONSTRUCTION

Our MitH formalization comprises as abstract and modular infrastructure that provides abstract classes for the cryptographic primitives that define the MitH protocol and a general MitH construction that does not consider any concrete implementation. This abstract infrastructure, formalized in `../generic-mith` folder, can then be instantiated with any primitive realization in order to obtain a concrete implementation of MitH. Our particular implementation instantiates the modular architecture with the Shamir secret sharing scheme, the BGW protocol and a SHA256-based commitment protocol but it is possible to instantiate it with other primitive realizations.

## Contents

Our EasyCrypt formalization can be found under the `src/` folder. The sub-folder structure mimics that of the abstract formalization.

- folder `General` - general definitions that are used multiple times in the implementation. Concretely:
  - `FieldPolynomial.ec` - interface for polynomials over field elements
pwd
- folder `Assumptions/` - cryptographic assumptions required by our proof. Concretely:
  - `CRPRF.ec` - formalization of collision resistance pseudo-random function (PRF)
  - `DiscreteLogAssumption.ec` - formalization of the discrete logarithm assumption
  - `RF.ec` - formalization of a random function
- folder `Circuit/` - circuit interface. Concretely:
  - `ArithmeticCircuit.ec` - arithmetic circuit implementation, that is a concrete realization of the abstract circuit interface
- folder `CommitmentScheme` - commitment scheme interface. Concretely:
  - `CRPRFCommitment.ec` - a concrete commitment scheme based on the a collision resistant PRF
- folder `Functionalities` - functionalities interface. Concretely:
  - `AGateFunctionality.ec` - functionality of a gate
  - `AdditionFunctionality.ec` - addition functionality
  - `MultiplicationFunctionality.ec` - multiplication functionality
  - `SMultiplicationFunctionality.ec` - scalar multiplication functionality
  - `ConstantFunctionality.ec` - constant functionality
  - `RefreshFunctionality.ec` - refresh functionality
  - `ArithmeticProtocolFunctionality.ec` - specific functionality for arithmetic protocols
- folder `MPC` - multiparty computation (MPC) interface. Concretely:
  - `AGate.ec` - abstract interface for the evaluation of gates
  - `GatePrivacy.ec` - gate's privacy
  - `GateWeak.ec` - gate's weak security
  - `WeakPrivacyComposition.ec` - composition result for weak privacy
  - `ProtocolWeak.ec` - protocol weak security
- folder `MPC/ArithmeticProtocol/` - interface for arithmetic protocols. Concretely
  - `AdditionGate.ec` - abstract interface for addition gates
  - `MultiplicationGate.ec` - abstract interface for multiplication gates
  - `SMultiplicationGate.ec` - abstract interface for scalar multiplication gates
  - `ArithmeticProtocol.ec` - interface for arithmetic protocols, that provides a general arithmetic circuit evaluation method based on the arithmetic gates above
- folder `MPC/BGW/` - formalization of the BGW protocol. Concretely:
  - `Addition.ec` - formalization of the BGW addition gate
  - `Multiplication.ec` - formalization of the BGW multiplication gate
  - `SMultiplication.ec` - formalization of the BGW scalar multiplication gate
  - `Refresh.ec` - formalization of the BGW refresh gate
  - `BGWGate.ec` - BGW gates
  - `BGW.ec` - formalization of the BGW protocol
- folder `SecretSharing` - secret sharing interface. Concretely:
  - `Shamir.ec` - formalization of the Shamir secret sharing scheme
- folder `MPCInTheHead` - formalization of MitH. Concretely:
  - `ShamirBGWSha256InTheHead.ec` - concrete formalization of the MitH protocol, instantiated with the Shamir secret sharing scheme, the BGW protocol and the hash-based commitment scheme (realized with the SHA256 hash function)


## Verifying the EasyCrypt formalization

The proof scripts of this formalization can be verified by the following command (tested with `Easycrypt commit: 4c419f4`, with provers `Z3-8.4.10` and `alt-ergo-2.4.0`):

`$> make check`


The simpler way of getting a working environment with all the needed dependencies is to use docker (`Dockerfile` given at the top-level directory). 
