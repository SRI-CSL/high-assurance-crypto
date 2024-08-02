# EVOCrypt: EasyCrypt Verified OCaml Cryptographic library

EVOCrypt is a library that provides verified, high-assurance implementations of a series of cryptographic algorithms/protocols, including
- Commitment schemes
- MPC protocols
- Secret sharing schemes
- ZK protocols

All implementations have been first specified in EasyCrypt, where all security and functional correctness proofs have been formalized. OCaml code is then obtained via code synthesis using the [CoCoCrypt](https://github.com/SRI-CSL/cococrypt) toolchain. The properties proved in EasyCrypt are carried out to the final OCaml implementation, thus increasing the degree of assurance of our code.

We next provide a detailed list of the concrete algorithms/protocols provided by EVOCrypt.

#### Commitment schemes

So far, we support the following commitment schemes:
- SHA3-based commitment scheme

#### MPC protocols

So far, we support the following MPC protocols:
- BGW protocol, with unlimited party support

#### Secret sharing schemes

So far, we support the following secret sharing schemes:
- Shamir secret sharing, with unlimited party support

#### ZK protocols

So far, we support the following ZK protocols:
- MPC-in-the-Head, using BGW as the underlying MPC protocol
- Line-Point Zero Knowledge (LPZK), assuming pre-computed correlated randomness

## Instalation requirements

EVOCrypt uses the following third-party tools/libraries:
- OCaml (>= 4.14.0) - available at [https://ocaml.org/](https://ocaml.org/)
- Dune (>= 3.14) - available at [https://github.com/ocaml/dune](https://github.com/ocaml/dune)
- Cryptokit - available at [https://github.com/xavierleroy/cryptokit](https://github.com/xavierleroy/cryptokit)
- Zarith - available at [https://github.com/ocaml/Zarith](https://github.com/ocaml/Zarith)
- Domainslib - available at [https://github.com/ocaml-multicore/domainslib](https://github.com/ocaml-multicore/domainslib)

We recommend installing the above dependencies using `opam`. However, they can be installed by cloning the corresponding repository and manually installing the tool/library.

After installing `OCaml` and `opam`, typing

```
$> opam install dune cryptokit zarith domainslib
```
installs all EVOCrypt required dependencies

## Installing/Compiling EVOCrypt

If installing from source, running

```
$> make
$> make install
```

builds and install the EVOCrypt library (under root module named `EVOCrypt`) assuming that all dependencies have been successfully installed. 

EVOCrypt can also be installed via `opam`, by running

```
$> opam install evocrypt
```

which installs EVOCrypt and its dependencies via `opam`.

## Examples

Examples of how to use EVOCrypt can be found in the `test` directory.

## EasyCrypt proof

The EasyCrypt proof can be found under the `proof` folder. To compile the proof, we include a Dockerfile that can be built via

```
$> docker build -t ec-check-docker -f Dockerfile .
```

and then executing it by running

```
$> docker run -ti --memory="16g" --cpus="3.0" ec-check-docker
```

Alternatively, from the main repository folder, doing

```
$> make check-proof
```

also builds and executed the proof checker Docker container.

## Acknowledgments

This material is based upon work supported by DARPA under Contract No. HR001120C0086. Any opinions, findings and conclusions or recommendations expressed in this material are those the author(s) and do not necessarily reflect the views of the United States Government or DARPA.

Distribution Statement ‘A’ (Approved for Public Release, Distribution Unlimited)