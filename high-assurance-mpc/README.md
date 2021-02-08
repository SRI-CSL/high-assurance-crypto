# VERIFIED IMPLEMENTATION OF BGW MPC PROTOCOL AND SHAMIR SECRET SHARING SCHEME

This project contains a security proof of the [BGW protocol](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/GBW88/GBW88.ps) and of the [Shamir secret sharing scheme](https://dl.acm.org/doi/pdf/10.1145/359168.359176), that was machine-checked using EasyCrypt. In addition, the project also contains a  verified OCaml implementation of these two primitives that was synthesized from the EasyCrypt proof.

## Table of contents

* [Folder contents](#folder-contents)
* [Proof organization](#proof-organization)
* [Verifying the EasyCrypt formalization](#verifying-the-easycrypt-formalization)
* [Verified implementation](#verified-implementation)
	* [Code organization](#code-organization)
	* [Building the verified implementation](#building-the-verified-implementation)

## Folder contents

The EasyCrypt formalization can be found under the `proof/` folder, whereas the source code of the verified implementation can be found under the `extraction/` folder. The `config` folder has the required configuration file needed to verify the proof.

## Proof organization

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
- folder `MPC` - multiparty computation (MPC) interface. Concretely:
	- `AGate.ec` - abstract interface for the evaluation of gates
	- `GatePrivacy.ec` - formalization of the privacy property for gates
- folder `ArithmeticProtocol/` - interface for arithmetic protocols. Concretely
	- `AdditionGate.ec` - abstract interface for addition gates
	- `MultiplicationGate.ec` - abstract interface for multiplication gates
	- `SMultiplicationGate.ec` - abstract interface for scalar multiplication gates
- folder `BGW/` - formalization of the BGW protocol. Concretely:
	- `BGWAddition.ec` - formalization of the BGW addition gate
	- `BGWMultiplication.ec` - formalization of the BGW multiplication gate
	- `BGWSMultiplication.ec` - formalization of the BGW scalar multiplication gate
- folder `SecretSharing` - secret sharing interface. Concretely:
	- `ASecretSharingScheme.ec` - abstract interface for secret sharing schemes
	- `SecretSharingSchemeSecurity.ec` - formalization of the security of secret sharing schemes
	- `Shamir.ec` - formalization of the Shamir secret sharing scheme

## Verifying the EasyCrypt formalization

Our EasyCrypt proof can be verified by typing

`$> make check-proof`

which will run the EasyCrypt test script against all files that comprise the formalization. Note that checking the proof might take a few minutes to complete.

## Verified implementation

Our verified implementation follows directly the same architecture of the proof, and is thus comprised of an abstract and modular infrastructure that provides abstract classes for the cryptographic primitives. This framework is fully reusable and can be used with other instantiations of MPC protocols or secret sharing schemes.

### Code organization
The source code (under `extraction/src/`) is organized as follows:
- folder `ECLib` - code of EasyCrypt libraries used in the proof. Concretely:
	- `Core.ml` - core EasyCrypt definitions
	- `CyclicGroup.ml` - EasyCrypt cyclic group library
	- `ECList.ml` - EasyCrypt list library
	- `Option.ml` - EasyCrypt option value
	- `PrimeField.ml` - EasyCrypt prime field library
- folder `General` - general definitions that are used multiple times in the implementation. Concretely:
	- `FieldPolynomial.ml` - interface for polynomials over field elements
	- `Utils.ml` - utilities, such as party identifiers and string converstion functions
- folder `MPC` - multiparty computation (MPC) interface. Concretely:
	- `AGate.ml` - abstract interface for the evaluation of gates
- folder `ArithmeticProtocol/` - interface for arithmetic protocols. Concretely
	- `AdditionGate.ml` - abstract interface for addition gates
	- `MultiplicationGate.ml` - abstract interface for multiplication gates
	- `SMultiplicationGate.ml` - abstract interface for scalar multiplication gates
- folder `BGW/` - implementation of the BGW protocol. Concretely:
	- `BGWAddition.ml` - implementation of the BGW addition gate
	- `BGWMultiplication.ml` - implementation of the BGW multiplication gate
	- `BGWSMultiplication.ml` - implementation of the BGW scalar multiplication gate
- folder `SecretSharing` - secret sharing interface. Concretely:
	- `ASecretSharingScheme.ml` - abstract interface for secret sharing schemes
	- `Shamir.ml` - implementation of the Shamir secret sharing scheme

### Building the verified implementation

#### Dependencies

The dependencies required by our BGW and Shamir implementations include:
- OCaml (available at http://caml.inria.fr/)
- OCamlbuild
- ZArith (available at https://github.com/ocaml/Zarith)
- Cryptokit (available at https://github.com/xavierleroy/cryptokit)
- Lymp (available at https://github.com/dbousque/lymp)

All these dependencies can be installed via `opam`, an OCaml package manager, as explained bellow.

1. Optionally, use opam to install the system dependencies

&ensp;&ensp;`$> opam install depext`
&ensp;&ensp;`$> opam depext ocamlbuild zarith cryptokit lymp`

2. Install dependencies

&ensp;&ensp;`$> opam install ocamlbuild zarith cryptokit lymp`

#### Building the source code

Once the dependencies have been successfully installed, the source code can be build inside the dedicated implementation folder `extraction/` folder by doing

&ensp;&ensp;`$> cd extraction`
&ensp;&ensp;`$> make`

which complies the code, producing an executable `mpcRun.native` that can be used to execute and benchmark our implementation and that the programmer can use as an example on how to use our verified implementation as a library to other software projects.