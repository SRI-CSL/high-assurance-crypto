# High-assurance, machine-checked security proof of LPZK and corresponding verified implementations

This project consists of a verified implementation of the Line-Point zero-knowledge (LPZK) proof protocol. LPZK is a family of protocols where a prover produces a proof by encoding the witness as an affine line v(x) = a*x + b and the verifier checks validity of the proof by querying the line at a single point x. The attractiveness of LPZK lies in its efficiency. Namely, proving satisfiability of (generic) arithmetic circuits requires only 2-5 times the computation of evaluating the circuit in the clear and the prover only communicates roughly 2 field elements per multiplication gate, making LPZK also attractive from a network point of view. LPZK is defined over the designated verifier non-interactive zero-knowledge (DVNIZK) model, where it is assumed that input-independent correlated randomness has been pre-processed and that the interaction between the prover and verifier consists of a single message sent by the former to the latter. The terminology designated verifier is used to attest that only a verifier holding correlated randomness with the prover is able to verify the proof produced by the prover.

In this work, we develop an end-to-end machine-checked implementation of LPZK, that was obtained from a series of (also machine-checked) optimization steps. In more detail, we start with a reference implementation of LPZK, for which we perform the machine-checked completeness, soundness, and zero-knowledge proofs. Next, we apply the following optimization steps:

* Optimization based on algorithmic re-design: where we optimize the specifications of both the prover and verifier
* Optimization based on the execution model: where we explore the usage of parallelism to speed up the computation
* Optimization based on memory management: where we replace and augment the data structures used to store input and randomness values in order to reduce access overhead

Our development was derived from a machine-checked security proof of LPZK that was developed in EasyCrypt, an interactive proof-assistant tailored for cryptographic proofs. All the afore mentioned optimization have also been formalized in EasyCrypt, before code was generated from the proof.

## Disclaimer

The reviewer may notice that some modifications to the folder were done January 23, therefore after then January 19 submission deadline. These modifications were done **ONLY** at the implementation level, not at the proof level. Concretely, the implementation version submitted January 19 was the test version, that **did not** use correlated randomness and, therefore, produced incorrect results. This version is faster to just benchmark the performance of the implementation without considering it's correctness. 

We have resubmitted the correct version, that creates correlated version before executing the protocol, thus producing the correct result.

## Project organization

We separate the different components of our project as follows:
- `proof` folder - contains the EasyCrypt development that formalizes the LPZK protocol and proves its security. It also includes the formal development of the optimization steps that comprise in this project.
- `extraction` - contains the OCaml implementation of the LPZK protocol. We provide two LPZK implementations: a list-based implementation and an array-based implementation. These implementations can be executed following a sequential execution model or resorting to parallelism.

Additionally, a `config` folder collects required configuration files used in build/verification infrastructure, and a `tests` folder contains a series of test circuits that can be used against the LPZK verified implementations.

## Installation

This project relies on a number of dependencies, detailed in each component presented above. For convenience, we provide a `Dockerfile` allowing to assemble a container with all the required dependencies preinstalled. To use the Docker (https://www.docker.com) container, simply type at the toplevel directory of the development:

```bash
$> docker build -t lpzk-docker .
$> docker run -ti lpzk-docker
```

Once inside the `lpzk-docker` container, the very same directory structure mentioned above is accessible.

NOTE: if Docker runs in a VM (e.g. when using docker-desktop for Windows or Mac), the memory limit should be set to at least 4GB.

## Running & Testing

The `Makefile` at the top level directory makes available the following targets:

- `build` - builds all versions of the LPZK implementation;
- `test-list <prime=P> <size=N> <cores=K>` - runs list-based LPZK implementation matrix multiplication of size N, over field P and using K cores;
- `test-array <prime=P> <size=N> <cores=K>` - runs array-based LPZK implementation matrix multiplication of size N, over field P and using K cores;

Notice that running these targets depends on the availability of the required dependencies. Typing just `make` shows a brief help with information on some additional targets. In addition, each component has specific `Makefile`s that may give access to some additional targets.
