open Domainslib

module LPZK : sig
    val generate_lpzk_prover_randomness : int -> LPZK.prover_rand_t

    val generate_lpzk_verifier_randomness : int -> LPZK.verifier_rand_t

    val parallel_generate_lpzk_prover_randomness : Task.pool -> int -> LPZK.prover_rand_t

    val parallel_generate_lpzk_verifier_randomness : Task.pool -> int -> LPZK.verifier_rand_t
end