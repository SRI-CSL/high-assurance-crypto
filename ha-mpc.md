# Computer-aided Verification and Synthesis of Secure Multiparty Computation (MPC) Protocols

This repository contains EasyCrypt formalization and other software for computer-aided verification and automated synthesis of high-assurance secure multiparty computation (MPC) protocols.

# Papers
* [A High-Assurance Evaluator for Machine-Checked Secure Multiparty Computation](https://eprint.iacr.org/2019/922)


## Table of contents
* [Papers](#papers)
* [Dependencies](#dependencies)
	* [OCaml](#ocaml)
	* [EasyCrypt](#easycrypt)
* [Local EasyCrypt build](#local-easycrypt-build)
	* [Configuring EasyCrypt](#configuring-easycrypt)
* [Software](#software)
	* [High-assurance MPC evaluator](#high-assurance-mpc)
	* [EasyCrypt extraction tool](#easycrypt-extraction-tool)


# Papers
* [A High-Assurance Evaluator for Machine-Checked Secure Multiparty Computation](https://eprint.iacr.org/2019/922)


## Dependencies

### OCaml

OCaml is a functional, statically-typed programming language from the ML family, offering a powerful module system extending that of Standard ML and a feature-rich, class-based object system.

OCaml comprises two compilers. One generates bytecode which is then interpreted by a C program. This compiler runs quickly, generates compact code with moderate memory requirements, and is portable to many 32 or 64 bit platforms. Performance of generated programs is quite good for a bytecoded implementation. This compiler can be used either as a standalone, batch-oriented compiler that produces standalone programs, or as an interactive REPL system.

The other compiler generates high-performance native code for a number of processors. Compilation takes longer and generates bigger code, but the generated programs deliver excellent performance, while retaining the moderate memory requirements of the bytecode compiler. 

OCaml is available at: https://ocaml.org.

#### Installing OCaml

OCaml installation instructions can be found at: https://ocaml.org/learn/tutorials/up_and_running.html

To better interop with the libraries available here, we highly recommend installing OCaml via OPAM.

### EasyCrypt

EasyCrypt is a toolset for reasoning about relational properties of probabilistic computations with adversarial code. Its main application is the construction and verification of game-based cryptographic proofs.

We use EasyCrypt to develop (and machine-check) the security and functional proofs that support our verified implementations. Therefore, EasyCrypt is required in order to verify our proofs. We provide a testing script that allows the verification of our proofs using the command line version of EasyCrypt. However, to use the interactive proof system of EasyCrypt, the installation of Proof General (and the appropriate Emacs configuration) is also required.

EasyCrypt is available at: https://www.easycrypt.info.

#### Installing EasyCrypt

A comprehensive description of the EasyCrypt installation instructions can be found at: https://www.easycrypt.info/trac/browser/README.md?rev=1.0. This document will also guide you through the installation of the dependencies required by EasyCrypt.

## Local EasyCrypt build

We include a local copy of the EasyCrypt repository under the `easycrypt/` folder. This is a git submodule, hence, the latest version of the EasyCrypt repository can be pulled via

```
$> cd easycrypt
$> git submodule init
$> git submodule update
```

Once all EasyCrypt dependencies have been installed, a dedicated copy of EasyCrypt can be build using

`$> make easycrypt`

which will create an EasyCrypt executable inside the `easycrypt/`  folder.

### Configuring EasyCrypt

After building EasyCrypt, add to the EasyCrypt configuration `~/.config/easycrypt/easycrypt.conf` (if file doesn't exist, create it) the following entries

```
[general]
idirs=General:path-to-repo/high-assurance-mpc/proof/src/General
idirs=Functionalities:path-to-repo/high-assurance-mpc/proof/src/Functionalities
idirs=SecretSharing:path-to-repo/high-assurance-mpc/proof/src/SecretSharing
idirs=MPC:path-to-repo/high-assurance-mpc/proof/src/MPC
idirs=ArithmeticProtocol:path-to-repo/high-assurance-mpc/proof/src/MPC/ArithmeticProtocol
idirs=BGW:path-to-repo/high-assurance-mpc/proof/src/MPC/BGW
```

where `path-to-repo` is the path to the value of `$> pwd`.

## Software

### High-assurance MPC

The `high-assurance-mpc` folder contains an EasyCrypt proof of the Shamir secret sharing scheme and of the BGW MPC protocol. Moreover, it also contains an OCaml verified implementation of these two cryptographic primitives, that was obtained using our EasyCrypt extraction tool.

A detailed explanation of the folder organization, as well as running instructions, can be found in its dedicated [README](https://github.com/SRI-CSL/high-assurance-crypto/high-assurance-mpc/README.md) file.

### EasyCrypt extraction tool


