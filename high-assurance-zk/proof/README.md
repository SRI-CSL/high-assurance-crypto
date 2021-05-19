
# FORMAL VERIFICATION OF "MPC-IN-THE-HEAD" BASED ZERO KNOWLEDGE PROTOCOL

This folder contains a proof of security of the MPC-in-the-Head (MitH) paradigm, that was machine-checked using EasyCrypt, an interactive theorem prover tailored for cryptographic proofs.

## Contents

Our MitH EasyCrypt formalization can be found under the `proof/` folder. In `easycrypt/`. Folder `config` has the required configuration file needed to verify the proof.

## Verifying the EasyCrypt formalization with Docker

Our EasyCrypt proof can be verified via the Dockerfile provided.

To build the Docker container, simply type (under the `/proof` folder)

`$> docker build -t proof-docker .`

You may have to have super user privilegies to do so. Then, it is possible to execute the Docker container via

`$> docker run -ti proof-docker`

which builds EasyCrypt and verifies every proof file. A green message displaying "True" will show if the file is successfully verified, whereas a red message displaying "False" will show if the file is not verified.

## Verifying the EasyCrypt formalization from source

### Building EasyCrypt

#### Building EasyCrypt dependencies

To install EasyCrypt dependencies, please follow the instructions in https://github.com/EasyCrypt/easycrypt/blob/1.0/README.md, which points to the README file inside EasyCrypt's main repository.

#### Building a local EasyCrypt copy

Once all EasyCrypt dependencies have been installed, a dedicated copy of EasyCrypt can be build using  

`$> make easycrypt`

which will create an EasyCrypt executable inside the `easycrypt` folder.

#### Configuring EasyCrypt

After building EasyCrypt, add to the EasyCrypt configuration ~/.config/easycrypt/easycrypt.conf (if file doesn't exist, create it) the following entries

```
[general]
idirs=General:path-to-folder/proof/src/General
idirs=Assumptions:path-to-folder/formal-zk/proof/src/Assumptions
idirs=Functionalities:path-to-folder/formal-zk/proof/src/Functionalities
idirs=Circuit:path-to-folder/formal-zk/proof/src/Circuit
idirs=SecretSharing:path-to-folder/formal-zk/proof/src/SecretSharing
idirs=MPC:path-to-folder/formal-zk/proof/src/MPC
idirs=ArithmeticProtocol:path-to-folder/formal-zk/proof/src/MPC/ArithmeticProtocol
idirs=BGW:path-to-folder/formal-zk/proof/src/MPC/BGW
idirs=CommitmentScheme:path-to-folder/formal-zk/proof/src/CommitmentScheme
idirs=ZeroKnowledge:path-to-folder/formal-zk/proof/src/ZeroKnowledge
idirs=SigmaProtocol:path-to-folder/formal-zk/proof/src/ZeroKnowledge/SigmaProtocol
idirs=InTheHead:/path-to-folder/formal-zk/proof/src/InTheHead
```

where `path-to-folder` is the path to the value of `$> pwd`

### Checking the proof

After all the above steps have been complete, the proof can be checked by typing

`$> make check-proof`

which will run the EasyCrypt test script against all files that comprise the formalization. Note that checking the proof might take a few minutes to complete.

## Proof organization

Our MitH formalization comprises as abstract and modular infrastructure that provides abstract classes for the cryptographic primitives that define the MitH protocol and a general MitH construction that does not consider any concrete implementation. This abstract infrastructure can then be instantiated with any primitive realization in order to obtain a concrete implementation of MitH. Our particular implementation instantiates the modular architecture with the Shamir secret sharing scheme, the BGW protocol and a SHA256-based commitment protocol but it is possible to instantiate it with other primitive realizations.


The proof code (under `proof/src/`) is organized as follows:

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
	- `ArithmeticProtocolFunctionality.ec` - specific functionality for arithmetic protocols

- folder `MPC` - multiparty computation (MPC) interface. Concretely:
	- `AGate.ec` - abstract interface for the evaluation of gates
	- `AProtocol.ec` - abstract interface for the evaluation of five party protocols
	- `ATwoPartyProtocol.ec` - abstract interface for two party protocols
	- `ProtocolPrivacy.ec` - formalization of the privacy property for protocols

- folder `ArithmeticProtocol/` - interface for arithmetic protocols. Concretely
	- `AdditionGate.ec` - abstract interface for addition gates
	- `MultiplicationGate.ec` - abstract interface for multiplication gates
	- `SMultiplicationGate.ec` - abstract interface for scalar multiplication gates
	- `ArithmeticProtocol.ec` - interface for arithmetic protocols, that provides a general arithmetic circuit evaluation method based on the arithmetic gates above

- folder `BGW/` - formalization of the BGW protocol. Concretely:
	- `BGWAddition.ec` - formalization of the BGW addition gate
	- `BGWMultiplication.ec` - formalization of the BGW multiplication gate
	- `BGWSMultiplication.ec` - formalization of the BGW scalar multiplication gate
	- `BGW.ec` - formalization of the BGW protocol

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

- folder `InTheHead` - formalization of MitH. Concretely:
	- `InTheHeadSigmaProtocol.ec` - modular interface that formalizes the MitH protocol based on the secret sharing, protocol and commitment scheme abstract interfaces and following a sigma protocol structure and that proves the completeness and soundness properties for any party configuration.
	- `InTheHeadSigmaProtocol5P.ec` - instance of the abstract MitH protocol for a concrete 5-party configuration and that proves the zero-knowledge property.
	- `ShamirBGWSha256InTheHead.ec` - concrete formalization of the MitH protocol, instantiated with the Shamir secret sharing scheme, the BGW protocol and the hash-based commitment scheme (realized with the SHA256 hash function)