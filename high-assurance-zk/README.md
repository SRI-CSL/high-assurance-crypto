# VERIFIED IMPLEMENTATION OF THE MPC-IN-THE-HEAD ZK PROTOCOL

The project contains a security proof of the [MPC-in-the-Head](https://web.cs.ucla.edu/~rafail/PUBLIC/77.pdf) (MitH) ZK proof protocol, instantiated with the [BGW protocol](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/GBW88/GBW88.ps) and with an hash-based commitment scheme, that was machine-checked using EasyCrypt. In addition, the project also contains a  verified OCaml implementation of these two primitives that was synthesized from the EasyCrypt proof.

To demonstrate the usability of our verified MitH implementation, we provide a wrapper that is able to take as input any relation described in the IR0 format and evaluate it by invoking our verified implementation.

## Table of contents
* [Papers](#papers)
* [Folder contents](#folder-contents)
* [Proof organization](#proof-organization)
* [Verifying the EasyCrypt formalization](#verifying-the-easycrypt-formalization)
* [Verified implementation](#verified-implementation)
	* [Code organization](#code-organization)
	* [Building the verified implementation](#building-the-verified-implementation)


* [Papers](#papers)



## Folder contents

The EasyCrypt formalization can be found under the `proof/` folder, whereas the source code of the verified implementation can be found under the `extraction/` folder. The `config` folder has the required configuration file needed to verify the proof.

## Proof organization

Our formalization comprises as abstract and modular infrastructure that provides abstract classes for MPC protocols, secret sharing and commitment schemes. These are used to derive the generic MitH result. This abstract framework is then instantiated with concrete protocols and executable code is derived from it. The proof code (under `proof/src/`) is organized as follows:

- folder `General` - general definitions that are used multiple times in the implementation. Concretely:
	- `CyclicGroup.ec` - EasyCrypt cyclic group library
	- `PrimeField.ec` - EasyCrypt prime field library
	- `FieldPolynomial.ec` - interface for polynomials over field elements
	- `Utils.ec` - utilitaries, such as party identifiers and string converstion functions
	- `ListExt.ec` - extensions to the EasyCrypt library
- folder `Assumptions/` - cryptographic assumptions required by our proof. Concretely:
	- `CRPRF.ec` - formalization of collision resistance pseudo-random function (PRF)
	- `DiscreteLogAssumption.ec` - formalization of the discrete logarithm assumption
	- `RF.ec` - formalization of a random function
- folder `Circuit/` - circuit interface. Concretely:
	- `ACircuit.ec` - abstract interface for the specification of circuits
	- `ArithmeticCircuit.ec` - arithmetic circuit implementation, that is a concrete realization of the abstract circuit interface
- folder `CommitmentScheme` - commitment scheme interface. Concretely:
	- `ACommitmentScheme.ec` - abstract interface for the specification of commitment schemes
	- `Binding.ec`  - formalization of the binding property
	- `Hiding.ec` - formalization of the hiding property
	- `CRPRFCommitment.ec` - a concrete commitment scheme based on the a collision resistant PRF
- folder `Functionalities` - functionalities interface. Concretely:
	- `AGateFunctionality.ec` - functionality of a gate
	- `AProtocolFunctionality.ec` - functionality of a protocol
	- `AdditionFunctionality.ec` - addition functionality
	- `MultiplicationFunctionality.ec` - multiplication functionality
	- `SMultiplicationFunctionality.ec` - scalar multiplication functionality
	- `RefreshFunctionality.ec` - refresh functionality
	- `ArithmeticProtocolFunctionality.ec` - specific functionality for arithmetic protocols
- folder `MPC` - multiparty computation (MPC) interface. Concretely:
	- `AGate.ec` - abstract interface for the evaluation of gates
	- `AProtocol.ec` - abstract interface for the evaluation of five party protocols
	- `ATwoPartyProtocol.ec` - abstract interface for two party protocols
	- `GatePrivacy.ec` - formalization of the privacy property for gates
	- `GateWeak.ec` - formalization of the _weak privacy_ security property for gates
	- `ProtocolPrivacy.ec` - formalization of the privacy property for protocols
	- `ProtocolWeak.ec` - formalization of the _weak privacy_ property for protocols
	- `WeakPrivacyComposition.ec` - formalization of the compositional property between a _weak_ protocol and a private gate, yielding a private protocol
- folder `ArithmeticProtocol/` - interface for arithmetic protocols. Concretely
	- `AdditionGate.ec` - abstract interface for addition gates
	- `MultiplicationGate.ec` - abstract interface for multiplication gates
	- `SMultiplicationGate.ec` - abstract interface for scalar multiplication gates
	- `ArithmeticProtocol.ec` - interface for arithmetic protocols, that provides a general arithmetic circuit evaluation method based on the arithmetic gates above
- folder `BGW/` - formalization of the BGW protocol. Concretely:
	- `Addition.ec` - formalization of the BGW addition gate
	- `Multiplication.ec` - formalization of the BGW multiplication gate
	- `SMultiplication.ec` - formalization of the BGW scalar multiplication gate
	- `BGWGate.ec` - formalization of the BGW protocol, without the final share refresh
	- `Refresh.ec` - formalization of the BGW refresh gate
	- `BGW.ec` - formalization of the full BGW protocol, as the composition of the BGW  gate with a refresh gate at the end
- folder `SecretSharing` - secret sharing interface. Concretely:
	- `ASecretSharingScheme.ec` - abstract interface for secret sharing schemes
	- `SecretSharingSchemeSecurity.ec` - formalization of the security of secret sharing schemes
	- `Shamir.ec` - formalization of the Shamir secret sharing scheme
- folder `ZeroKnowledge` - zero-knowledge proof protocol interface. Concretely:
	- `AZKProof.ec` - abstract interface for zero-knowledge proof protocols
	- `AZKFunctionality.ec` - abstract interface for zero-knowledge functionalities
	- `Completeness.ec` - formalization of the completeness property
- folder `SigmaProtocol` - sigma protocol interface. Concretely:
	- `ASigmaProtocol.ec` - abstract interface for sigma protocols
	- `SigmaProtocolCompleteness.ec` - formalization of the completeness property for sigma protocols
	- `SigmaProtocolSoundness.ec` - formalization of the soundness property for sigma protocols
	- `SigmaProtocolZeroKnowledge.ec` - formalization of the zero-knowledge property for sigma protocols
- folder `MPCInTheHead` - formalization of MitH. Concretely:
	- `InTheHeadSigmaProtocol.ec` - modular interface that formalizes the MitH protocol based on the secret sharing, protocol and commitment scheme abstract interfaces and following a sigma protocol structure and that proves the completeness and soundness properties for any party configuration.
	- `InTheHeadSigmaProtocol5P.ec` - instance of the abstract MitH protocol for a concrete 5-party configuration and that proves the zero-knowledge property.
	- `ShamirBGWSha256InTheHead.ec` - concrete formalization of the MitH protocol, instantiated with the Shamir secret sharing scheme, the BGW protocol and the hash-based commitment scheme (realized with the SHA256 hash function)

## Verifying the EasyCrypt formalization

Our EasyCrypt proof can be verified via the Dockerfile provided.

To build the Docker container, simply type (under the `/proof` folder)  

`$> docker build -t proof-docker .`

You may have to have super user privilegies to do so. Then, it is possible to execute the Docker container via

`$> docker run -ti proof-docker`

which builds EasyCrypt and verifies every proof file. A green message displaying "True" will show if the file is successfully verified, whereas a red message displaying "False" will show if the file is not verified.

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
	- `RF.ml` - generic definition of a random function
	- `CRPRF.ml` - interface for collision resistance pseudo-random function (PRF)
- folder `Circuit/` - circuit interface. Concretely:
	- `ACircuit.ml` - abstract interface for the specification of circuits
	- `ArithmeticCircuit.ml` - arithmetic circuit implementation, that is a concrete realization of the abstract circuit interface
- folder `MPC` - multiparty computation (MPC) interface. Concretely:
	- `AGate.ml` - abstract interface for the evaluation of gates
	- `AProtocol.ml` - abstract interface for the evaluation of five party protocols
	- `ATwoPartyProtocol` - abstract interface for two party protocols
	- `WeakPrivacyComposition.ml` - abstract interface for the composition of a _weak_ secure protocol with a private protocol
- folder `ArithmeticProtocol/` - interface for arithmetic protocols. Concretely
	- `AdditionGate.ml` - abstract interface for addition gates
	- `MultiplicationGate.ml` - abstract interface for multiplication gates
	- `SMultiplicationGate.ml` - abstract interface for scalar multiplication gates
- folder `BGW/` - implementation of the BGW protocol. Concretely:
	- `BGWAddition.ml` - implementation of the BGW addition gate
	- `BGWMultiplication.ml` - implementation of the BGW multiplication gate
	- `BGWSMultiplication.ml` - implementation of the BGW scalar multiplication gate
	- `BGWGate.ml` - implementation of the BGW protocol, without the final share refresh
	- `BGWRefresh.ml` - implementation of the BGW refresh gate
	- `BGW.ml` - implementation of the full BGW protocol, as the composition of the BGW gate with a refresh gate at the end
- folder `SecretSharing` - secret sharing interface. Concretely:
	- `ASecretSharingScheme.ml` - abstract interface for secret sharing schemes
	- `Shamir.ml` - implementation of the Shamir secret sharing scheme
- folder `CommitmentScheme` - commitment scheme interface. Concretely:
	- `ACommitmentScheme.ml` - abstract interface for the specification of commitment schemes
	- `CRPRFCommitment.ml` - a concrete commitment scheme based on the a collision resistant PRF
- folder `ZeroKnowledge` - zero-knowledge proof protocol interface. Concretely:
	- `AZKProof.ml` - abstract interface for zero-knowledge proof protocols
	- `ASigmaProtocol.ml` - abstract interface for sigma protocols
- folder `InTheHead` - implementation of MitH. Concretely:
	- `InTheHead.ml` - modular interface that specifies the MitH protocol based on the secret sharing, protocol and commitment scheme abstract interfaces
	- `ShamirBGWSha256InTheHead.ml` - concrete implementation of the MitH protocol, instantiated with the Shamir secret sharing scheme, the BGW protocol and the hash-based commitment scheme (realized with the SHA256 hash function)

### Building the verified implementation

The dependencies required by our MitH implementation include
- OCaml (available at http://caml.inria.fr/)
- OCamlbuild
- ZArith (available at https://github.com/ocaml/Zarith)
- Cryptokit (available at https://github.com/xavierleroy/cryptokit)
- Lymp (available at https://github.com/dbousque/lymp)
- Containers (available at https://github.com/c-cube/ocaml-containers)
- ppx_deriving (available at https://github.com/ocaml-ppx/ppx_deriving)
- Yojson (available at https://github.com/ocaml-community/yojson)

All these dependencies can be installed via `opam`, an OCaml package manager, as explained bellow.

#### Installing opam

On Ubuntu and derivatives:

&ensp;&ensp;`$> add-apt-repository ppa:avsm/ppa`
&ensp;&ensp;`$> apt-get update`
&ensp;&ensp;`$> apt-get install ocaml ocaml-native-compilers camlp4-extra opam`

On Fedora/OpenSUSE

&ensp;&ensp;`$> sudo dnf update`
&ensp;&ensp;`$> sudo dnf install ocaml ocaml-docs ocaml-camlp4-devel opam`

On MacOSX (using brew)

&ensp;&ensp;`$> brew install opam`

#### Installing OCaml

OCaml can be installed via opam by typing

&ensp;&ensp;`$> opam switch create 4.11.0`

which installs the 4.11.0 version of the OCaml language. After installing `opam` and `ocaml`, run the following

&ensp;&ensp;`$> opam init`
&ensp;&ensp;`$> eval $(opam env)`

#### Installing packages

1. Optionally, use opam to install the system dependencies

&ensp;&ensp;`$> opam install depext`
&ensp;&ensp;`$> opam depext ocamlbuild zarith cryptokit lymp containers ppx_deriving yojson`

2. Install dependencies

&ensp;&ensp;`$> opam install ocamlbuild zarith cryptokit lymp containers ppx_deriving yojson`

#### Building the source code

Once the dependencies have been successefuly installed, the source code can be build inside the dedicated implementation folder `extraction/` folder by doing

&ensp;&ensp;`$> cd extraction`
&ensp;&ensp;`$> make benchmark`

which complies the code, producing an executable `benchmark.native` that builds an OCaml script that benchmarks the implementations derived from the EasyCrypt proof.
