## MPC in the Head implementation using a Jasmin Implementation of Maurer\'s protocol

The contents of this folder are as follows:

- `src` - OCaml code extracted from EasyCrypt using the semi-automatic process
    described in the paper. The following files contain manually added code:

    * The `MPC/Maurer` folder contains the orchestration code for Maurer\'s protocol, where
    the `NextMsgMaurerAPI_<backend>.ml` files (for each of the 3 Maurer backends) contains manually added code to
    interface the Jasmin implementation in place of the Maurer5Spec.ec specification used in the proofs. A few other files in this folder (namely 'NextMsgECArray.ml', 'NextmsgEcBindings.ml', 'NextMsgECInt.ml', 'NextMsgECList.ml', 'NextMsgEcPervasive.ml', 'NextMsgIMap.ml' and 'NextMsgISet.ml') correspond to abstract interfaces that are extracted from the EasyCrypt proofs and manually instantiated with bindings to external OCaml libraries for common types such as lists, maps , arrays and respective common operations.
    * `CommitmentScheme/CRPRFCommitmentWrapper.ml` interfaces the hash-based
    commitment.
    * `SecretSharing/MaurerSS.ml` interfaces the Jasmin implementation 
    of the secret sharing scheme for Maurer\'s protocol.
    
    All other files were extracted from EasyCrypt and all of them,
    except the ones mentioned above, exactly match the ones used
    for the BGW instantiation.
- `maurer.c` - Unverified C code that handles interface with Jasmin
- `MPC*.s` - verified assembly code for Maurer\'s protocol (compilation of `Maurer5_jazz.jazz`) file from the Maurer Jasmin implementation.
- `sha3.c` - this is a cross-platform implementation of SHA3, rather
than the AVX2 implementation we mention in the paper which only 
works on a restricted set of architectures.
- `shake128-m.c` - wrapper around the `sha3.c` implementation that is called by `maurer.c`

In `tests`, we provide simple examples that can be used to test the implementation.
In `benchs`, we provide larger examples that can be used to benchmark the implementation.

## Building the executable

### Dependencies

To execute the code, you will need opam and a number of dependencies.
For example, in a fresh RedHat linux instance, the following sequence of commands will build the necessary dependencies.

```bash
$> sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
$> sudo yum groupinstall 'Development Tools'
$> sudo yum install bubblewrap
$> sudo yum install pcre-devel gmp-devel zlib-devel
$> opam init
$> opam install ../config/dependencies.opam
$> eval $(opam env)
```

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





