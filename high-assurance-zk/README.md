# High-assurance, machine-checked security proof of MPC-in-the-Head and corresponding verified implementations

This project consists of a verified implementation of the MPC-in-the-Head (MitH) zero-knowledge proof protocol. MitH is a generic construction that yields a zero-knowledge protocol for arbitrary relations. Briefly, MitH accepts relations that are represented as circuits that can be securely evaluated by a Multiparty Computation (MPC) protocol. The prover emulates the MPC protocol “in its head”, obtaining a set of views observed by the parties. It then prepares commitments for each of the views (using any “binding” and “hiding” commitment scheme) and sends those commitments to the verifier. The verifier can then challenge the prover with a set of parties which it wants to “open” (i.e., see the views of those parties) -- the size of this set depends on the specific MPC protocol instantiating the construction. The prover then opens those views to the verifier which accepts the proof iff:
- it receives valid views with respect to the commitments 
- the local output of each challenged party is TRUE 
- the messages observed in the two views are “consistent”, meaning that the incoming messages of on view are consistent with the outgoing messages of the other view.

Our verified implementation is twofold. On one hand, we provide a verified implementation of MitH that relies on the BGW protocol combined with a PRF-based commitment scheme. On the other hand, we provide a verified implementation of MitH that uses Maurer’s construction as the MPC protocol. 

Both implementations were derived from a (modular) machine-checked security proof of the MitH paradigm that was developed in EasyCrypt, an interactive proof-assistant tailored for cryptographic proofs. Our generic security result was then be instantiated with the selected protocols to derive concrete security results for the two realizations that we provide in this project.

## Project organization

We separate the different components of our project as follows:
- `generic-mith` folder ([README](./generic-mith/README.md)) - contains the EasyCrypt development that formalizes the generic MitH framework and proves its security from the properties of abstract components such as MPC protocols, secret-sharing schemes and commitment schemes. It also includes the formalization of general results on Zero-Knowledge Interactive Proof-Systems (c.f. `MetaArguments`);
- `mith-bgw` folder ([README](./mith-bgw/README.md)) - contains the EasyCrypt development that instantiates the generic MitH framework with a specification of the BGW protocol;
- `mith-maurer` folder ([README](./mith-maurer/README.md)) - contains the EasyCrypt development that instantiates the generic MitH framework with a specification of Maurer’s MPC protocol, as well as correctness proofs for Jasmin's low-level implementation;
- `implementation-bgw` ([README](./implementation-bgw/README.md)) - contains the OCaml implementation of the MitH framework instantiated with the BGW protocol, that was extracted from the EasyCrypt specification;
- `implementation-maurer` ([README](./implementation-maurer/README.md)) - contains the OCaml implementation of the MitH framework instantiated with Maurer’s MPC protocol, that was extracted from the EasyCrypt specification. The core secret-sharing and gate operations in the specification are replaced by an external Jasmin library, that is called within OCaml via a C wrapper

Each folder has a dedicated README file with an additional explanation of its contents and dependencies. Additionally, a `config` folder collects required configuration files used in build/verification infrastructure.

## Installation

This project relies on a number of dependencies, detailed in each component presented above. For convenience, we provide a `Dockerfile` allowing to assemble a container with all the required dependencies preinstalled. To use the Docker (https://www.docker.com) container, simply type at the toplevel directory of the development:

```bash
$> docker build -t mith-docker .
$> docker run -ti mith-docker
```

Once inside the `mith-docker` container, the very same directory structure mentioned above is accessible.

NOTE: if docker runs in a VM (e.g. when using docker-desktop for windows or mac), the memory limit should be set to 4GB.

## Running & Testing

The `Makefile` at the top level directory makes available the following targets:

- `build-all` - builds the executables;
- `test-all` - runs some tests for all executables;
- `check-all` - check all the EasyCrypt proof scripts (can take up to a couple of hours).
- `cloc-all` - global LineOfCode figures
- `cloc-comps` - LineOfCode counts per component

Notice that running these targets depends on the availability of the required dependencies. Typing just `make` shows a brief help with information on some additional targets.
In addition, each component has a specific `Makefile` that may give access to some additional targets. In particular, the `implementation-bgw` and `implementation-maurer` folders contain additional instructions on how to run and test each implementation.
