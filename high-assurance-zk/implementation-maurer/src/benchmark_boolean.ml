open ECList
open ECCore
open ECOption
   
(*open Aux
open NextMsgMaurerCircuit
open NextMsgMaurerGate
open NextMsgMaurerP
open NextMsgMaurerR
open NextMsgMaurerMPC
open MaurerProtocol*)

open NextMsgECCore
open NextMsgMaurerP
open NextMsgMaurerProtocol
open NextMsgMaurerCompat

open MaurerShake128InTheHeadBenchmark

open InTheHeadBenchmark

external prover_rand_gen : int -> int -> int -> (int Array.t * (int Array.t Array.t) * (int Array.t)) = "prover_rand_gen_c"                                                     
(* pid, number of pins, number of sins, number of randomnesses -> comr add, sins, rands, msgs *)
external write_opening : int -> int -> int -> int -> unit  = "write_opening"
external read_opening : int -> int -> int -> int -> (int * int Array.t * int Array.t * int Array.t)  = "read_opening"

let parse_json = fun fs ->
  let t0 = Sys.time () in
  
  let statement, wit = Jsonload_maurer.parse_maurer_files (fs) in
  let modulus = statement.header.field_characteristic in

  let instance  = statement.instance
                  |> List.rev
                  |> List.fold_left (fun sofar a -> Cons(a,sofar)) Nil
  in
  let wit = wit
            |> List.rev
            |> List.fold_left (fun sofar a -> Cons(a,sofar)) Nil
  in
  let circuit = statement.relation in
  let t1 = Sys.time () in
  let tparse = (t1 -. t0) *. 1000. in

  Format.printf "File parsed and loaded in %f milliseconds\n@." tparse ;

  (circuit,instance,wit,modulus)

let verifier_randomness_generator =
  let r1 = ref 0 in
  let r2 = ref 0 in
  let quit_loop = ref false in
  Random.self_init () ;
  
  while not !quit_loop do
    let r1' = Random.int 5 in
    let r2' = Random.int 5 in
    if r1' <> r2' then
      begin r1 := r1' ; r2 := r2' ; quit_loop := true ; end
  done ;
  (!r1, !r2)

let benchmark_8 benchmark n =
  let nf = Z.to_float (Z.of_string n) in
  let rec median8 t1 t2 t3 t4 t5 t6 t7 t8 = function
    | Nil -> (t1 /. nf, t2 /. nf, t3 /. nf, t4 /. nf, t5 /. nf, t6 /. nf, t7 /. nf, t8 /. nf)
    | Cons((a,b,c,d,e,f,g,h), s) -> median8 (t1 +. a) (t2 +. b) (t3 +. c) (t4 +. d) (t5 +. e) (t6 +. f) (t7 +. g) (t8 +. h) s
  in
  let b_n = ECList.init (Z.of_string n) (fun _ -> benchmark ()) in
  median8 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 b_n

let isprover = ref false
let isverifier = ref false
let chal1 = ref 0 
let chal2 = ref 1
let options = [("-prover", Arg.Set isprover, "Run prover");
               ("-verifier", Arg.Set isverifier, "Run verifier");
               ("-pid1", Arg.Set_int chal1, "First challenge pid");
               ("-pid2", Arg.Set_int chal2, "Second challenge pid");]
let usage_message = "zkRun [-prover|-verifier] <json input1> <json input2> ..."
let args = ref []

let response_bandwidth = ref 0

let () =
  Arg.parse options (fun a->args := a::!args) usage_message;

  Format.printf "Prover = %b Verifier = %b Pid1 = %d Pid2 = %d\n Loading the relation, witness and instance from file...@." !isprover !isverifier !chal1 !chal2;

  let n = List.hd !args in
  args := List.tl !args ;

  let (circuit,instance,wit,modulus) = parse_json (List.rev !args) in
  let (topo, gg) = circuit in
  let (np,ns,m,q) = topo in
  let nsinputs = Z.to_int ns in
  let npinputs = Z.to_int np in
  let nwires = Z.to_int q + npinputs + nsinputs in
  let n_rounds =  Z.add (Z.of_int 1) q in
  Format.printf "Initialized n_rounds to %d\n@." (Z.to_int n_rounds);

  let rec z_list_to_maurer = function
    | Nil -> Nil
    | Cons (x, xs) -> Cons ((Z.to_int x, 0, 0, 0), z_list_to_maurer xs)
  in

  let rec z_list_to_string = function
    | Nil -> ""
    | Cons (x, Nil) -> Z.to_string x
    | Cons (x, xs) -> Z.to_string x ^ ", " ^ z_list_to_string xs
  in

  Format.printf "Parsed instance: %s\nParsed witness: %s\n\n@." (z_list_to_string instance) (z_list_to_string wit) ;
  Format.printf "Circuit topology: #public inputs = %s | #secret inputs = %s | #output wires = %s | #gates = %s\n@." (Z.to_string np) (Z.to_string ns) (Z.to_string m) (Z.to_string q) ;
  let module MaurerRelation = struct
      let relc = (gg , (Z.add np ns, NextMsgISet.ISet.oflist (iota_ Z.zero (size instance))))
    end in
  
  (* Format.printf "Gates \n %s\n@." (maurer_gates_list_to_string gg); *)

  let module Maurer = MaurerShake128InTheHead (MaurerRelation) in
  
  let pins = z_list_to_maurer instance in
  let sins = z_list_to_maurer wit in
  let i = !chal1 in
  let j = !chal2 in
  let pi = Z.of_int i in
  let pj = Z.of_int j in
  let cs = let open MaurerSS in map (fun pid -> (pid, ())) MaurerSS.pid_set in

  let rec build_rand r i = function
    | Nil -> Nil
    | Cons (MaurerGate.Const wid_c, xs) ->  Cons (Aux.L (), build_rand r (i+1) xs)
    | Cons (MaurerGate.Add wl_wr_wc, xs) -> Cons (Aux.L (), build_rand r (i+1) xs)
    | Cons (MaurerGate.Mul wl_wr_wc, xs) -> Cons (Aux.R r.(i), build_rand r (i+1) xs)
    | Cons (MaurerGate.SMul wl_wr_wc, xs) -> Cons (Aux.L (), build_rand r (i+1) xs) in

  let  build_msgs p m gg = 
    let lm = Cons (Aux.R (m.(Z.to_int (size gg))+p*4*6*8), Nil) in
    let rec build_msgs' i =
      function
      | Nil -> lm
      | Cons (MaurerGate.Const wid_c, xs) ->  Cons (Aux.L (), build_msgs' (i+1) xs)
      | Cons (MaurerGate.Add wl_wr_wc, xs) -> Cons (Aux.L (), build_msgs' (i+1) xs)
      | Cons (MaurerGate.Mul wl_wr_wc, xs) -> Cons (Aux.R (m.(i)+p*4*6*8), build_msgs' (i+1) xs)
      | Cons (MaurerGate.SMul wl_wr_wc, xs) -> Cons (Aux.L (), build_msgs' (i+1) xs) 
    in
    build_msgs' 0 gg
  in

  let write_response(r : Maurer.response_t) = 
    let (r1,r2) = r in
    let k1 = snd r1 in
    let (x1, (rands1, ims1)) = fst r1 in
    let nrands1 = Z.to_int (size rands1) in
    let npins1 = Z.to_int (size (fst x1)) in
    let nsins1 = Z.to_int (size (snd x1)) in
    let k2 = snd r2 in
    let (x2, (rands2, ims2)) = fst r2 in
    let nrands2 = Z.to_int (size rands2) in
    let npins2 = Z.to_int (size (fst x2)) in
    let nsins2 = Z.to_int (size (snd x2)) in
    write_opening (Z.to_int (fst k1)) npins1 nsins1 nrands1; 
    write_opening (Z.to_int (fst k2)) npins2 nsins2 nrands2;
    (NextMsgMaurerAPI.viewSize (npins1 + nsins1 + nrands1) * 8,
     NextMsgMaurerAPI.viewSize (npins2 + nsins2 + nrands2) * 8)
  in

  let read_response (pi  : int) (pj : int) (npins : int) (nsins : int)  (nrands: int) : Maurer.response_t =
    let (kk1,xs1,rss1,mm1) = 
      read_opening pi npins nsins nrands in
    let xx1 = (pins, array_to_eclist xs1) in
    let rands1' = build_rand rss1 0 (fst MaurerRelation.relc) in
    let mm1p (p:int) : MaurerReveal.ST.rmsgs = 
          NextMsgArray.Array.of_list (build_msgs p mm1 (fst MaurerRelation.relc)) in
    let mm1ps : MaurerReveal.ST.prmsgs = MaurerP.init (fun p -> mm1p (Z.to_int p) ) in
    let (kk2,xs2,rss2,mm2) = 
        read_opening pj npins nsins nrands in
    let xx2 = (pins, array_to_eclist xs2) in
    let rands2' = build_rand rss2 0 (fst MaurerRelation.relc) in
    let mm2p (p:int) : MaurerReveal.ST.rmsgs = 
         NextMsgArray.Array.of_list (build_msgs p mm2 (fst MaurerRelation.relc)) in
    let mm2ps : MaurerReveal.ST.prmsgs = MaurerP.init (fun p -> mm2p (Z.to_int p) ) in
        (
          ((xx1,(rands1',(witness,mm1ps))),(Z.of_int pi,kk1)) 
        ,
          ((xx2,(rands2',(witness,mm2ps))),(Z.of_int pj,kk2)) 
        )
  in

  let benchmark () =
 
    let t0 = Sys.time () in
    let (r_ss, r_mpc, r_cs) = prover_rand_gen npinputs nsinputs nwires in
    let t1 = Sys.time () in
    let prand_time = (t1 -. t0) *. 1000. in

    let t0 = Sys.time() in
    let (i,j) = verifier_randomness_generator in
    let t1 = Sys.time () in
    let vrand_time = (t1 -. t0) *. 1000. in
  
    let rs0 = build_rand r_mpc.(0) 0 (fst MaurerRelation.relc) in
    let rs1 = build_rand r_mpc.(1) 0 (fst MaurerRelation.relc) in
    let rs2 = build_rand r_mpc.(2) 0 (fst MaurerRelation.relc) in
    let rs3 = build_rand r_mpc.(3) 0 (fst MaurerRelation.relc) in
    let rs4 = build_rand r_mpc.(4) 0 (fst MaurerRelation.relc) in
    
    let rss = map (fun i -> r_ss.(Z.to_int i)) (iota_ Z.zero ns) in
    let rs = Cons ((Z.of_int 0, rs0), Cons ((Z.of_int 1, rs1), Cons ((Z.of_int 2, rs2), Cons ((Z.of_int 3, rs3), Cons ((Z.of_int 4, rs4), Nil))))) in
    let rcs1 = (Z.of_int 0, (Z.of_int 0, r_cs.(0))) in
    let rcs2 = (Z.of_int 1, (Z.of_int 1, r_cs.(1))) in
    let rcs3 = (Z.of_int 2, (Z.of_int 2, r_cs.(2))) in
    let rcs4 = (Z.of_int 3, (Z.of_int 3, r_cs.(3))) in
    let rcs5 = (Z.of_int 4, (Z.of_int 4, r_cs.(4))) in
    let rcs = Cons (rcs1, Cons (rcs2, Cons (rcs3, Cons (rcs4, Cons (rcs5, Nil))))) in
    
    let (ps, cs) = Maurer.commitment (rss, rs, rcs) (sins,pins) in

    let (vs, chl) = Maurer.challenge (Z.of_int i, Z.of_int j) pins cs in

    let resp = Maurer.response ps chl in
    
    let (sizei, sizej) = write_response (resp) in
    response_bandwidth := sizei + sizej ;

    let resp_com = read_response i j npinputs nsinputs (Z.to_int q) in 
    
    let final = Maurer.check vs resp_com in
    (prand_time, vrand_time, !mpc_time, !pcommit_time, !challenge_time, !response_time, !vcommit_time, !check_time)
  in

  (*(prand_time, vrand_time, !mpc_time, !pcommit_time, !challenge_time, !response_time, !vcommit_time, !check_time)*)
    
  Format.printf "Running benchmarks for MitH instantiated with Maurer protocol with N = 5 and T = 2\n\n@." ;
    
  let (prand_time, vrand_time, mpc_time, pcommit_time, challenge_time, response_time, vcommit_time, check_time) = benchmark_8 benchmark n in
  Format.printf "MitH benchmark result:\n\tProver:\n\t\tCommitment phase:\n\t\t\tRandom generation: %f ms\n\t\t\tMPC protocol: %f ms\n\t\t\tCommit: %f ms\n\t\t\tTotal: %f ms\n\t\tResponse: %f ms\n\n\tVerifier:\n\t\tRandom generation: %f ms\n\t\tChallenge: %f ms\n\t\tDecision phase:\n\t\t\tCommit: %f ms\n\t\t\tCheck: %f ms\n\t\t\tTotal: %f ms\n\n\tProver total time: %f ms\n\tVerifier total time: %f ms\n\tProtocol time: %f ms\n\nBandwidth:\n\tCommitment: 160 B\n\tResponse: %d B@." prand_time mpc_time pcommit_time (prand_time +. mpc_time +. pcommit_time) response_time vrand_time challenge_time vcommit_time check_time (vcommit_time +. check_time) (prand_time +. mpc_time +. pcommit_time +. response_time) (vrand_time +. challenge_time +. vcommit_time +. check_time) (prand_time +. mpc_time +. pcommit_time +. response_time +. vrand_time +. challenge_time +. vcommit_time +. check_time) !response_bandwidth

