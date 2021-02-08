open ECList

type pid_mpc_t = P1 | P2 | P3 | P4 | P5
type pid_zk_t = Prover | Verifier

let p1 = ref Z.zero
let p2 = ref Z.zero
let p3 = ref Z.zero
let p4 = ref Z.zero
let p5 = ref Z.zero

let shares_to_string x =
  let (x1,x2,x3,x4,x5) = x in
  "(" ^ Z.to_string x1 ^ ", " ^ Z.to_string x2 ^ ", " ^ Z.to_string x3 ^ ", " ^ Z.to_string x4 ^ ", " ^ Z.to_string x5 ^ ")"

let rec shares_list_to_string = function
  | Nil -> ""
    | Cons (x, Nil) -> shares_to_string x
    | Cons (x,xs) -> shares_to_string x ^ " || " ^ shares_list_to_string xs

  let secret_to_string x = Z.to_string x

  let rec secret_list_to_string = function
    | Nil -> ""
    | Cons (x, Nil) -> secret_to_string x
    | Cons (x,xs) -> secret_to_string x ^ " || " ^ secret_list_to_string xs
