# Formal verification of the BGW MPC protocol and of the Shamir secret sharing scheme

Our proof of the [BGW protocol](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/GBW88/GBW88.ps) and of the [Shamir secret sharing scheme](https://dl.acm.org/doi/pdf/10.1145/359168.359176) comprises abstract definitions of an MPC gate and of secret sharing schemes, as well as the security properties surrounding these primitives. The concrete BGW and Shamir implementations are then obtained by instantiating these abstract definitions, and proving that they achieve the correponding security properties.

## Contents

Our MPC formalization comprises as abstract and modular infrastructure that provides abstract classes for an MPC protocol. The proof code (under `proof/src/`) is organized as follows:

- folder `General` - general definitions that are used multiple times in the implementation. Concretely:
	- `CyclicGroup.ec` - EasyCrypt cyclic group library
	- `ListExt.ec` - extensions to EasyCrypt list library
	- `PrimeField.ec` - EasyCrypt prime field library
	- `FieldPolynomial.ec` - interface for polynomials over field elements
- folder `Functionalities` - functionalities interface. Concretely:
	- `AGateFunctionality.ec` - functionality of a gate
	- `AdditionFunctionality.ec` - addition functionality
	- `MultiplicationFunctionality.ec` - multiplication functionality
	- `SMultiplicationFunctionality.ec` - scalar multiplication functionality
	- `RefreshFunctionality.ec` - _refresh_ functionality
- folder `MPC` - multiparty computation (MPC) interface. Concretely:
	- `AGate.ec` - abstract interface for the evaluation of gates
	- `GatePrivacy.ec` - formalization of the privacy property for gates
	- `GateWeak.ec` - formalization of a _weak_ version of the privacy property for gates
- folder `ArithmeticProtocol/` - interface for arithmetic protocols. Concretely
	- `AdditionGate.ec` - abstract interface for addition gates
	- `MultiplicationGate.ec` - abstract interface for multiplication gates
	- `SMultiplicationGate.ec` - abstract interface for scalar multiplication gates
- folder `BGW/` - formalization of the BGW protocol. Concretely:
	- `Addition.ec` - formalization of the BGW addition gate
	- `Multiplication.ec` - formalization of the BGW multiplication gate
	- `SMultiplication.ec` - formalization of the BGW scalar multiplication gate
	- `Refresh.ec` - formalization of the _refresh_ gates
- folder `SecretSharing` - secret sharing interface. Concretely:
	- `ASecretSharingScheme.ec` - abstract interface for secret sharing schemes
	- `SecretSharingSchemeSecurity.ec` - formalization of the security of secret sharing schemes
	- `Shamir.ec` - formalization of the Shamir secret sharing scheme

## Verifying the EasyCrypt formalization

The proof scripts of this formalization can be verified by the following command (tested with `Easycrypt commit: 4c419f4`, with provers `Z3-8.4.10` and `alt-ergo-2.4.0`):

`$> make check`


The simpler way of getting a working environment with all the needed dependencies is to use docker (`Dockerfile` given at the top-level directory).