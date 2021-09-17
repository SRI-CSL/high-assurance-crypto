# High-assurance Cryptographic Protocols and Algorithms

This repository contains SRI's public work focusing on computer-aided verification and automated synthesis of high-assurance cryptographic protocols and algorithms. Bellow, we provide a list of the developed projects, each one accompanied by a brief summary. Each project is linked to its respective folder, where the content of the project, together with a more detailed explanation of the work carried out, can be found.

## Projects

### [Computer-aided Verification and Synthesis of Secure Multiparty Computation (MPC) Protocols](https://github.com/SRI-CSL/high-assurance-crypto/tree/main/high-assurance-mpc)

The project consisted on formally verifying MPC protocols using EasyCrypt, where we formalized standard security notions of MPC and developed an EasyCrypt proof and implementation of the BGW addition and multiplication gates. In addition, other security properties of MPC protocols (such as proactive security) were explored. Finally, we constructed a (preliminary) EasyCrypt code extraction tool, that was used to obtain a verified implementation of the BGW protocol gates in OCaml.

### [Machine-checked ZKP for NP-relations: Formally Verified Security Proofs and Implementations of MPC-in-the-Head](https://github.com/SRI-CSL/high-assurance-crypto/tree/main/high-assurance-zk)

The project consisted on the formal verification of the [MPC-in-the-Head](https://web.cs.ucla.edu/~rafail/PUBLIC/77.pdf) (MitH) protocol in EasyCrypt. We identify three main contributions of this work. First, the formalization of the generic MitH construction, proving that the intrinsic security properties of zero-knowledge protocols (completeness, soundness and zero-knowledge) can be reduced to the security properties of the underlying MPC and commitment scheme protocols. Second, we provide an instantiation of the formalized MitH construction based on the BGW protocol, by taking advantage of the previous project, and improved the existing EasyCrypt extraction tool to derive a verified implementation of the (concrete) MitH protocol. Finally, we provide another instantiation of the MitH protocol based on the MPC protocol proposed by [Maurer](https://crypto.ethz.ch/publications/files/Maurer02b.pdf). This protocol was implemented in Jasmin, giving a high-speed, low-level implementation of such protocol, that was then connected to the generic MitH formalization.


## Team
- [Karim Eldefrawy](https://keldefrawy.github.io/)
- [Stéphane Graham-Lengrand](http://www.csl.sri.com/users/sgl/)
- [Vitor Pereira](https://scholar.google.com/citations?user=SvnICwIAAAAJ&hl=en)
- [Hadas Zeilberger](https://www.linkedin.com/in/hadas-zeilberger)

## Relevant links

- [EasyCrypt](https://www.easycrypt.info/)
- [Jasmin](https://github.com/jasmin-lang/jasmin)
- [OCaml](https://ocaml.org/)
