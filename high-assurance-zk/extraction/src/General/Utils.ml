open ECList

type pid_mpc_t = Z.t
                            
type pid_zk_t = Prover | Verifier

let p1 = ref (Z.of_string "1")
let p2 = ref (Z.of_string "2")
let p3 = ref (Z.of_string "3")
let p4 = ref (Z.of_string "4")
let p5 = ref (Z.of_string "5")

let pid_mpc_set : pid_mpc_t list = Cons (!p1, Cons (!p2, Cons (!p3, Cons (!p4, Cons (!p5, Nil)))))

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
                                                   
