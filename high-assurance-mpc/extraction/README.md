
# Verified implementation of the BGW protocol gates and of the Shamir secret sharing scheme

The present folder contains the code for a verified implementation of the addition, multiplication, scalar multiplication and _refresh_ gates of the BGW protocol. In addition, it also contains a verified implementation of the Shamir secret sharing scheme. To demonstrate the usability of our verified implementations, we provide a wrapper that benchmarks the execution times of each primitive.

## Contents

Our verified implementation follows directly the same architecture of the proof, and is thus comprised of an abstract and modular infrastructure that provides abstract classes for the cryptographic primitives. This framework is fully reusable and can be used with other instantiations of MPC protocols or secret sharing schemes.

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
- folder `MPC/ArithmeticProtocol/` - interface for arithmetic protocols. Concretely
  - `AdditionGate.ml` - abstract interface for addition gates
  - `MultiplicationGate.ml` - abstract interface for multiplication gates
  - `SMultiplicationGate.ml` - abstract interface for scalar multiplication gates
  - `RefreshGate.ml` - abstract interface for _refresh_ gates
- folder `MPC/BGW/` - implementation of the BGW protocol. Concretely:
  - `BGWAddition.ml` - implementation of the BGW addition gate
  - `BGWMultiplication.ml` - implementation of the BGW multiplication gate
  - `BGWSMultiplication.ml` - implementation of the BGW scalar multiplication gate
  - `BGWRefresh` - implementation of the BGW _refresh_ gate
- folder `SecretSharing` - secret sharing interface. Concretely:
  - `ASecretSharingScheme.ml` - abstract interface for secret sharing schemes
  - `Shamir.ml` - implementation of the Shamir secret sharing scheme

## Building the executable

### Dependencies

The dependencies required by our BGW and Shamir implementation include

- OCaml (available at http://caml.inria.fr/)
- OCamlbuild
- ZArith (available at https://github.com/ocaml/Zarith)
- Cryptokit (available at https://github.com/xavierleroy/cryptokit)
- Lymp (available at https://github.com/dbousque/lymp)
- Containers (available at https://github.com/c-cube/ocaml-containers)

All these dependencies can be installed via `opam` (https://opam.ocaml.org), an OCaml package manager.

We remind that the docker container given at the top-level directory of the development already includes all the dependencies.

### Compile & Run

Having dependencies successfully installed, the source code can be built by typing:

&ensp;&ensp;`$> make build`

If you encounter any compilation error, please run:

`$> make clean`

and retry the build.

You can then run the benchmarks with the following command:

`$> ./benchmark.native -field F -n N -t T -r R`

where `F` is the field size (must be prime), `N` is the number of parties of the protocol, `T` is the number of tolerated corrupt parties and `R` is the number of benchmark repetitions.
