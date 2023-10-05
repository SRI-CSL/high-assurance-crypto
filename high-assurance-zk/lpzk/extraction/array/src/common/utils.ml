open Containers

let print s i = Tracing.print Format.stdout s i

let args : string list ref = ref [] (* Where the command-line argument will be stacked *)

let parse_val s =
  let colon_split = String.split_on_char ':' s in
  let s = List.nth colon_split 1 in
  let comma_split = String.split_on_char ',' s in
  let s = List.nth comma_split 0 in
  let aspas_split = String.split_on_char '\"' s in
  Z.of_string (List.nth aspas_split 1)

let read_val ic =
  let line = input_line ic in
  parse_val line, ic

let create_jobs_for circ job_array =
  let nb_outputs = List.length circ in
  let n = Array.length job_array in
  let gates_per_job = nb_outputs / n in
  print "create_jobs" 1
    "@,@[%i output wires for %i jobs makes %i output wires per job@]@,"
    nb_outputs n gates_per_job;
  let () = if gates_per_job <= 0 then
             job_array.(0) <- circ
           else
             let circ = ref circ in
             for i = 0 to n-1 do
               let out, rest = List.take_drop gates_per_job !circ in
               job_array.(i) <- out;
               circ := rest
             done
  in
  gates_per_job