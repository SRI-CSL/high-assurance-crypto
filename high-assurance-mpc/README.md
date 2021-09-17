# Verified implementation of the BGW MPC protocol and of the Shamir secret sharing scheme

This project consists of a verified implementation of the BGW MPC protocol and of the Shamir secret sharing scheme. Our implementation was derived from a machine-checked security proof of both primitives developed in EasyCrypt, an interactive proof-assistant tailored for cryptographic proofs.

## Project organization

We separate the different components of our project as follows:
- `proof` folder ([README]()) - contains the EasyCrypt development that formalizes the BGW protocol gates and proves its security
- `extraction` folder ([README]()) - contains the OCaml implementation of the BGW gates, that was extraction from the EasyCrypt specification

Each folder has a dedicated README file with an additional explanation of its contents and dependencies. Additionally, a `config` folder collects required configuration files used in build/verification infrastructure.

## Installation

This project relies on a number of dependencies, detailed in each component presented above. For convenience, we provide a `Dockerfile` allowing to assemble a container with all the required dependencies preinstalled. To use the Docker (https://www.docker.com) container, simply type at the toplevel directory of the development:

```bash
$> docker build -t bgw-docker .
$> docker run -ti bgw-docker
```

Once inside the `bgw-docker` container, the very same directory structure mentioned above is accessible.

NOTE: if docker runs in a VM (e.g. when using docker-desktop for windows or mac), the memory limit should be set to 4GB.

## Running & Testing

The `Makefile` at the top level directory makes available the following targets:

- `build` - builds a benchmark executable for the BGW gates implementations
- `check` - checks all the EasyCrypt proof scripts

Notice that running these targets depends on the availability of the required dependencies. Typing just `make` shows a brief help with information on some additional targets.
