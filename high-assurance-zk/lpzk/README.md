# High-assurance, machine-checked security proof of LPZK and corresponding verified implementations

This project consists of a verified implementation of the [Line-Point Zero Knowledge](https://eprint.iacr.org/2020/1446)(https://eprint.iacr.org/2022/552) (LPZK) protocol. LPZK is a lightweight ZK protocol that leverages a (pre-processing) vector oblivious linear evaluation (VOLE) protocol to generate a designated-verifier ZK protocol. Briefly, in LPZK, the prover encodes the witness as an affine line `v(t) = at + b` (the VOLE expression) and the verifier queries the line at a single point `t = &alpha;`.

The focus of this work was to not only produce a verified implementation of the LPZK protocol, but also to address some core performance challenges facing computer-aided cryptography by presenting a formal treatment for accelerating such verified implementations based on two generic optimizations: one based on parallelism and another based on optimized memory accesses. All optimizations are first formally verified inside EasyCrypt, and then executable code is automatically synthesized from each step of the formalization. Our final code matches the performance of the manual LPZK implementation given in [1](https://eprint.iacr.org/2022/552).

# Information on proofs/code availability

We are currently waiting for the final open-source approval to disclose both the EasyCrypt proofs and the verified LPZK implementations. We will update this repository as soon as we receive the final green light.