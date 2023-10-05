open Yojson
open Yojson.Safe
open Yojson.Safe.Util
open Containers
open Domainslib

open Common
open LPZK
open Utils

open Jsonload

let rand_t () =
  let coef = ref Z.zero in
  let quit = ref false in

  while not !quit do
    coef := dt () ;
    if not (Z.equal !coef Z.zero) then quit := true
  done ;
  !coef

let dummy_rand_prover prime = { a = Z.div prime (ofint 143) ;
                         b = Z.div prime (ofint 17) ;
                         a' = Z.div prime (ofint 397) ;
                         b' = Z.div prime (ofint 85) }

let real_rand_prover prime = { a = rand_t () ;
                         b = rand_t () ;
                         a' = rand_t () ;
                         b' = rand_t () }

let get_prover_rand (topo : topology_t) (prime : Z.t) : prover_rand_t =
  Format.printf "Loading randomness...@." ;

  let total_rand = Z.add (Z.add topo.npinputs topo.nsinputs) topo.ngates in

  let rp = Array.make (Z.to_int (Z.add (Z.add total_rand (Z.of_int 2)) Z.one)) def_ui in
    
  for i = 0 to Z.to_int (Z.add total_rand (Z.of_int 2)) do
    let u = real_rand_prover prime in
    Array.set rp i u ;
  done ;

  Format.printf "Randomness loaded to memory %s@." (Z.to_string (size rp));
    
  rp

let dummy_rand_verifier alpha u = { v = fadd (fmul alpha u.a) u.b ;
                                    v' = fadd (fmul alpha u.a') u.b' }

let get_verifier_rand (topo : topology_t) (prime : Z.t) (rp : prover_rand_t) : verifier_rand_t =
  Format.printf "Loading randomness...@." ;

  let total_rand = Z.add (Z.add topo.npinputs topo.nsinputs) topo.ngates in

  let rv = Array.make (Z.to_int (Z.add (Z.add total_rand (Z.of_int 2)) Z.one)) def_yi in
  let alpha = rand_t () in

  for i = 0 to Z.to_int (Z.add total_rand (Z.of_int 2)) do
    let yi = dummy_rand_verifier alpha rp.(i) in
    Array.set rv i yi ;
  done ;

  Format.printf "Randomness loaded to memory@." ;

  { alpha = alpha ; y = rv }

let pad_witness l ws = 
  let pad = Array.make (Z.to_int l) Z.zero in
  Array.append pad ws

let tasks = ref 32

let timer_input  = Timer.create "inputs"

let timer_send   = Timer.create "send"
let timer_random_prover = Timer.create "random-prover"
let timer_commit = Timer.create "commit"

let timer_recv   = Timer.create "recv"
let timer_random_verifier = Timer.create "random-verifier"
let timer_prove  = Timer.create "prove"

let commitment statement witness =

  let instance      = statement.instance in
  let topo, circuit = statement.relation in

  let witness = pad_witness topo.npinputs witness in

  Timer.start timer_random_prover;

  Format.printf "Generating prover randomness...@." ;

  let rp = get_prover_rand topo !q in

  Timer.transfer timer_random_prover timer_commit;
  Format.printf "Prover randomness generated in %f ms@." (Timer.read timer_random_prover *. 1000.);
  Format.printf "Producing commitment message...@." ;

  let pool        = Task.setup_pool ~num_domains:(!tasks-1) () in
  let jobs        = Array.make !tasks [] in
  let _chunk_size = Utils.create_jobs_for circuit jobs in
  (* let default = PInputZ(Z.zero,{m = Z.zero; m' = Z.zero; c2 = Z.zero}), (Z.zero, Z.zero) in *)
  let treat1gate gg = commit rp (witness, ((topo, gg), instance)) in
  let aux i job =
    Utils.print "commit" 1 "@,@[Task %i starting@]@]%!@[<v>" i;
    let chunk = List.map treat1gate job in
    Marshal.to_bytes chunk [No_sharing]
  in

  let results = List.init !tasks (fun i -> Task.async pool (fun () -> aux i jobs.(i))) in

  let c = Task.run pool (fun () -> List.map (Task.await pool) results) in

  Timer.stop timer_commit;
  Format.printf "Commitment message generated in %f ms@." (Timer.read timer_commit *. 1000.);
  Task.teardown_pool pool ;

  (c, rp)

let decide statement cs rp =

  let instance      = statement.instance in
  let topo, circuit = statement.relation in
  let header        = statement.header in

  Timer.start timer_random_verifier;
  Format.printf "Generating verifier randomness...@." ;

  (*let rp = parse_randomness_msg !circuit_ref rp in*)
  let rv = get_verifier_rand topo !q rp in

  Timer.transfer timer_random_verifier timer_prove;
  Format.printf "Randomness generated in %f ms.@." (Timer.read timer_random_verifier *. 1000.) ;
  Format.printf "Checking proof...@." ;

  let pool = Task.setup_pool ~num_domains:(!tasks-1) () in
  let n    = Array.length cs in
  let jobs = Array.make n [] in
  let _chunk_size = Utils.create_jobs_for circuit jobs in

  let aux job cs =
    let cs = Marshal.from_bytes cs 0 in
    List.fold_left2 (fun b gg ci -> prove rv ((topo, gg), instance) ci && b) true job cs
  in

  let multitask () =
    Task.parallel_for_reduce ~start:0 ~finish:(n-1)
      ~body:(fun i -> aux (jobs.(i)) (cs.(i))) pool (&&) true;
  in

  let final = Task.run pool multitask in
  
  Timer.stop timer_prove;  
  Format.printf "Proof checked in %f ms.@." (Timer.read timer_prove *. 1000.);
  Format.printf "Decision = %s@." (if final then "TRUE" else "FALSE");
  Task.teardown_pool pool ;

  final

let run () =
  if Array.length Sys.argv < 5 then Printf.eprintf "./lpzkRun relation instance witness cores\n"
  else
    let relation_file = Sys.argv.(1) in
    let instance_file = Sys.argv.(2) in
    let witness_file  = Sys.argv.(3) in
    tasks := int_of_string Sys.argv.(4) ;

    Timer.start timer_input;

    Format.printf "Parsing relation, instance and witness files...@." ;
    let statement, witness, nmul =
      Jsonload.parse_files [relation_file; instance_file; witness_file]
    in
    let instance      = statement.instance in
    let topo, circuit = statement.relation in
    let header        = statement.header in
    q := header.field_characteristic ;
    
    Timer.stop timer_input ;
    Format.printf "Relation, instance and witness (%i multiplications) parsed in %f ms.@."
      nmul
      (Timer.read timer_input *. 1000.) ;
    Format.printf "Field size: %s@." (Z.to_string !q) ;

    let (c,rp) = commitment statement witness in
    let b = decide statement (Array.of_list c) rp in

    ()
;;

run ()
