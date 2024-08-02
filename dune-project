(lang dune 3.14)

(name evocrypt)

(generate_opam_files true)

(source
 (github SRI-CSL/evocrypt))

(authors "Vitor Pereira and Stéphane Graham-Lengrand")

(maintainers "Vitor Pereira <vitor.pereira@sri.com>")

(license "MIT License")

; (documentation https://url/to/documentation)

(package
 (name evocrypt)
 (synopsis "EVOCrypt: EasyCrypt Verified OCaml Cryptographic Library")
 (description "EVOCrypt includes verified implementations of modern cryptographic algorithms including MPC protocols (BGW and Maurer), commitment schemes (SHA3-based), ZK protocols (MPC-in-the-Head and LPZK) and OLE/VOLE protocols based on additively homomorphic encryption schemes (Paillier-based OLE/VOLE). All implementations were developed and proven secure in EasyCrypt and were then extracted to OCaml using CoCoCrypt")
 (depends ocaml dune cryptokit zarith domainslib)
 )

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
