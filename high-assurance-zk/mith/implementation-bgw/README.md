
# Verified evaluator engine for ZKP-MitH (based on BGW)

The present folder contains the code for a verified implementation of the MPC-in-the-Head (MitH) ZK proof protocol, instantiated with the BGW protocol and with a PRF-based commitment scheme. The implementation was derived from a machine-checked proof developed in the EasyCrypt proof assistant, an interactive theorem prover tailored for cryptographic proofs. To demonstrate the usability of our verified MitH implementation, we provide a wrapper that is able to take as input any relation described in the IR0 format and evaluate it by invoking our verified implementation.

## Contents

The MitH implementation can be found under the `src/` folder.

In `tests`, we provide simple examples that can be used to test the implementation.
In `benchs`, we provide larger examples that can be used to benchmark the implementation.

## Building the executable

### Dependencies

The dependencies required by our MitH BGW implementation include

- OCaml (available at http://caml.inria.fr/)
- OCamlbuild
- ZArith (available at https://github.com/ocaml/Zarith)
- Cryptokit (available at https://github.com/xavierleroy/cryptokit)
- Lymp (available at https://github.com/dbousque/lymp)
- Containers (available at https://github.com/c-cube/ocaml-containers)
- ppx\_deriving (available at https://github.com/ocaml-ppx/ppx_deriving)
- Yojson (available at https://github.com/ocaml-community/yojson)

All these dependencies can be installed via `opam` (https://opam.ocaml.org), an OCaml package manager.

We remind that the docker container given at the top-level directory of the development already includes all the dependencies.

### Compile & Run

Having dependencies successfully installed, the source code can be built by typing:

&ensp;&ensp;`$> make build`

If you encounter any compilation error, please run:

`$> make clean`

and retry the build.

You can then run the tests and benchmarks with any of the following two commands:

`$> make test`

`$> make bench`

