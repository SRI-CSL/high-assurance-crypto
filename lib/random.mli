open Domainslib

module LPZK : sig
    val generate_lpzk_prover_randomness : int -> Lpzk.prover_rand_t

    val generate_lpzk_verifier_randomness : int -> Lpzk.verifier_rand_t

    val parallel_generate_lpzk_prover_randomness : Task.pool -> int -> Lpzk.prover_rand_t

    val parallel_generate_lpzk_verifier_randomness : Task.pool -> int -> Lpzk.verifier_rand_t
end