let iteri = fun n f st -> let st = ref st in let i = ref Z.zero in while (Z.lt !i n) do st := f !i !st ; i := Z.add !i Z.one done ; !st


let logical_equality = fun x y -> x = y


let witness = Obj.magic None


let q = ref Z.one (* FILL ME! *)


let fmul = fun a b -> Z.erem (Z.mul a b) !q


let fadd = fun a b -> Z.erem (Z.add a b) !q


let fumin = fun a -> Z.erem (Z.neg a) !q


let finv = fun a -> Z.erem (Z.neg a) !q


let fsub = fun a b -> Z.erem (Z.sub a b) !q


let fdiv = fun a b -> Z.erem (Z.mul a (Z.invert b !q)) !q


let fexp = fun a b -> Z.powm a b !q


let ofint = fun x -> Z.erem (Z.of_int x) !q


let toint = fun x -> Z.to_int x


let dt : unit -> Z.t = fun _ -> Z.rem (Z.of_bits (Cryptokit.Random.string Cryptokit.Random.secure_rng 128)) !q


let fst4 x = let (a,b,c,d) = x in a


let snd4 x = let (a,b,c,d) = x in b


let trd4 x = let (a,b,c,d) = x in c


let frt4 x = let (a,b,c,d) = x in d


let range n = List.init n (fun i -> i)


let forall = fun n f st -> List.for_all (fun i -> f i st) (range n)


open Array

type witness_t = (Z.t) array

type instance_t = (Z.t) array

type topology_t = {
  npinputs: Z.t;
  nsinputs: Z.t;
  ngates: Z.t;
  noutputs: Z.t;
  }

type gates_t =
  | PInput of (Z.t)
  | SInput of (Z.t)
  | Constant of (Z.t) * (Z.t)
  | Addition of (Z.t) * gates_t * gates_t
  | Multiplication of (Z.t) * gates_t * gates_t

type circuit_t = (topology_t * gates_t)

type statement_t = (topology_t * gates_t) * ((Z.t) array)

let rec nth : type a. a -> (a array) -> (Z.t) ->  a =
  fun x xs n -> Array.get xs (Z.to_int n)

let boolean_and (b1: bool) (b'1: bool) : bool = b1 && b'1

let boolean_or (b1: bool) (b'1: bool) : bool = b1 || b'1

let valid_topology (topo : topology_t) : 
  bool =
  (let np = topo.npinputs in
  let ns = topo.nsinputs in
  let q = topo.ngates in
  let m = topo.noutputs in
  boolean_and (boolean_and (boolean_and (boolean_and (Z.leq (Z.zero) (np)) (Z.lt (Z.zero) (ns))) (Z.lt (Z.zero) m)) (Z.lt (Z.zero) q)) (Z.leq (m) (q)))

let rec valid_input_gates (np : Z.t) (ns : Z.t) (gg : gates_t) : 
  bool = 
  match gg with
  | PInput w -> boolean_and (Z.leq (Z.zero) (w)) (Z.lt (w) (np))
  | SInput w -> boolean_and (Z.leq (np) (w)) (Z.lt (w) (Z.add (np) (ns)))
  | Constant (_, _) -> true
  | Addition (_, wl, wr) -> boolean_and (valid_input_gates np ns wl) (valid_input_gates np ns wr)
  | Multiplication (_, wl, wr) -> boolean_and (valid_input_gates np ns wl) (valid_input_gates np ns wr)

let valid_constant_gates (np : Z.t) (ns : Z.t) (gg : gates_t) : 
  bool = 
  true

let rec get_gid (g: gates_t) : Z.t =
  match g with
  | PInput wid -> wid
  | SInput wid -> wid
  | Constant (gid, c3) -> gid
  | Addition (gid, wl, wr) -> gid
  | Multiplication (gid, wl, wr) -> gid

let rec mem_gid (k : Z.t) (gg : gates_t) : 
  bool =
  match gg with
  | PInput w -> logical_equality (w) (k)
  | SInput w -> logical_equality (w) (k)
  | Constant (gid, c) -> logical_equality (gid) (k)
  | Addition (gid, wl, wr) -> 
    boolean_or (boolean_or (logical_equality (gid) (k)) (mem_gid k wl))
                (mem_gid k wr)
  | Multiplication (gid, wl, wr) ->
    boolean_or (boolean_or (logical_equality (gid) (k)) (mem_gid k wl))
                (mem_gid k wr)

let boolean_not (b1: bool) : bool = not b1

let rec valid_gids np ns q (gg : gates_t) : 
  bool =
  match gg with  
  | PInput _ -> true
  | SInput _ -> true
  | Constant (gid, _) -> boolean_and (Z.leq (Z.add (np) (ns)) gid) (Z.lt (gid) (Z.add (np) (Z.add (ns) (q))))
  | Addition (gid, wl, wr) -> 
      boolean_and (boolean_and (boolean_and (boolean_and 
                  (boolean_and (Z.leq (Z.add (np) (ns)) gid) (Z.lt (gid) (Z.add (Z.add (np) (ns)) (q))))
                    (Z.lt (get_gid wl) (gid))) (Z.lt (get_gid wr) (gid)))
                    (boolean_and (boolean_not (mem_gid (gid) (wl))) (boolean_not (mem_gid (gid) (wr)))))
                    (boolean_and (valid_gids (np) (ns) (q) (wl)) (valid_gids (np) (ns) (q) (wr)))
  | Multiplication (gid, wl, wr) -> 
      boolean_and (boolean_and (boolean_and (boolean_and 
                  (boolean_and (Z.leq (Z.add (np) (ns)) gid) (Z.lt (gid) (Z.add (Z.add (np) (ns)) (q)))) 
                    (Z.lt (get_gid wl) (gid))) (Z.lt (get_gid wr) (gid)))
                    (boolean_and (boolean_not (mem_gid (gid) (wl))) (boolean_not (mem_gid (gid) (wr)))))
                    (boolean_and (valid_gids (np) (ns) (q) (wl)) (valid_gids (np) (ns) (q) (wr)))

let valid_gates (topo : topology_t) (gg : gates_t) = 
  boolean_and (boolean_and (valid_input_gates topo.npinputs topo.nsinputs gg)  
              (valid_constant_gates topo.npinputs topo.nsinputs gg))
              (valid_gids topo.npinputs topo.nsinputs topo.ngates gg)

let valid_circuit (c : topology_t * gates_t) : 
  bool =
  let (topo, gg) = c in boolean_and (valid_topology topo) ( valid_gates topo gg)

let rec eval_gates (gg: gates_t) (xp: (Z.t) array) (xs: (Z.t) array) : 
  Z.t =
  match gg with
  | PInput w -> nth (Z.zero ) xp w
  | SInput w -> nth (Z.zero ) xs w
  | Constant (gid, c) -> c
  | Addition (gid,
    wl,
    wr) ->
    (let result = eval_gates wr xp xs in
     let o = let result1 = eval_gates wl xp xs in fadd  result1 in o result)
  | Multiplication (gid,
    wl,
    wr) ->
    (let result = eval_gates wr xp xs in
     let o = let result1 = eval_gates wl xp xs in fmul  result1 in o result)

let eval_circuit (c: topology_t * gates_t) (xp: (Z.t) array) (xs: (Z.t) array) :
  Z.t = let (topo, gg) = c in eval_gates gg xp xs

let relation (w: (Z.t) array) (x: (topology_t * gates_t) * ((Z.t) array)) :
  bool =
  let (c,
  inst) =
  x in
  let result = eval_circuit c inst w in logical_equality result (Z.zero )

let relation1 (w: (Z.t) array) (x: (topology_t * gates_t) * ((Z.t) array)) :
  bool = relation w x

type prover_input_t = ((Z.t) array) * ((topology_t * gates_t) * ((Z.t) array))

type verifier_input_t = (topology_t * gates_t) * ((Z.t) array)

type ui_t = {
  a: Z.t;
  b: Z.t;
  a': Z.t;
  b': Z.t;
  }

type ui_t1 = ui_t

let def_ui = { a = Z.zero ; b = Z.zero ; a' = Z.zero ; b' = Z.zero  }

let def_ui1 = def_ui

type u_t = ui_t array

type prover_rand_t = ui_t array

let rec valid_rand_gates (r: ui_t array) (gg1: gates_t) : bool =
  match gg1 with
  | PInput wid -> true
  | SInput wid -> true
  | Constant (gid, c1) -> true
  | Addition (gid,
    wl,
    wr) ->
    (let result = valid_rand_gates r wr in
     let result1 = valid_rand_gates r wl in boolean_and result1 result)
  | Multiplication (gid,
    wl,
    wr) ->
    (let result = valid_rand_gates r wr in
     let result1 = valid_rand_gates r wl in boolean_and result1 result)

let valid_rand_gates1 (r: ui_t array) (gg1: gates_t) : bool =
  valid_rand_gates r gg1

let rec size : type a. (a array) ->  (Z.t) =
  fun xs -> Z.of_int (Array.length xs) 

let valid_rand_prover (r: ui_t array)
                      (x:
                      ((Z.t) array) * ((topology_t * gates_t) * ((Z.t) array))) :
  bool =
  let (w,
  st) =
  x in
  let (c1,
  inst1) =
  st in
  let (topo1,
  gg1) =
  c1 in
  let o =
    let o1 =
      let o2 =
        let o3 =
          let o4 =
            nth def_ui
            r
            (Z.sub (Z.add (Z.add (Z.add topo1.nsinputs topo1.npinputs)
                           topo1.ngates)
                    (Z.of_string "2"))
             Z.one) in
          o4.a in
        logical_equality o3 (Z.zero ) in
      boolean_not o2 in
    let o2 =
      let result = size r in
      logical_equality result
      (Z.add (Z.add (Z.add topo1.nsinputs topo1.npinputs) topo1.ngates)
       (Z.of_string "2")) in
    boolean_and o2 o1 in
  let result = valid_rand_gates r gg1 in
  boolean_and result o

let valid_rand_prover1 (r: ui_t array)
                       (x:
                       ((Z.t) array) * ((topology_t * gates_t) * ((Z.t) array)))
                       : bool = valid_rand_prover r x

type yi_t = {
  v: Z.t;
  v': Z.t;
  }

type yi_t1 = yi_t

let def_yi = { v = Z.zero ; v' = Z.zero  }

let def_yi1 = def_yi

type y_t = yi_t array

type verifier_rand_t = {
  alpha: Z.t;
  mutable y: yi_t array;
  }

type verifier_rand_t1 = verifier_rand_t

type prover_output_t = unit

type verifier_output_t = bool

type zi_t = {
  m: Z.t;
  m': Z.t;
  c2: Z.t;
  }

type zi_t1 = zi_t

type z_t =
  | PInputZ of (Z.t) * zi_t
  | SInputZ of (Z.t) * zi_t
  | ConstantZ of (Z.t) * zi_t
  | AdditionZ of (Z.t) * zi_t * z_t * z_t
  | MultiplicationZ of (Z.t) * zi_t * z_t * z_t

let is_pinputz (z : z_t) : bool =
  match z with
  | PInputZ (_, _) -> true
  | SInputZ (_, _) -> false
  | ConstantZ (_, _) -> false
  | AdditionZ (_, _, _, _) -> false
  | MultiplicationZ (_, _, _, _) -> false

let is_sinputz (z : z_t) : bool =
  match z with
  | PInputZ (_, _) -> false
  | SInputZ (_, _) -> true
  | ConstantZ (_, _) -> false
  | AdditionZ (_, _, _, _) -> false
  | MultiplicationZ (_, _, _, _) -> false

let is_constantz (z : z_t) : bool =
  match z with
  | PInputZ (_, _) -> false
  | SInputZ (_, _) -> false
  | ConstantZ (_, _) -> true
  | AdditionZ (_, _, _, _) -> false
  | MultiplicationZ (_, _, _, _) -> false

let is_additionz (z : z_t) : bool =
  match z with
  | PInputZ (_, _) -> false
  | SInputZ (_, _) -> false
  | ConstantZ (_, _) -> false
  | AdditionZ (_, _, _, _) -> true
  | MultiplicationZ (_, _, _, _) -> false

let as_additionz (z : z_t) =
  match z with
  | PInputZ (_, _) -> witness
  | SInputZ (_, _) -> witness
  | ConstantZ (_, _) -> witness
  | AdditionZ (gid, zi, zl, zr) -> (gid, zi, zl, zr)
  | MultiplicationZ (_, _, _, _) -> witness

let is_multiplicationz (z : z_t) : bool =
  match z with
  | PInputZ (_, _) -> false
  | SInputZ (_, _) -> false
  | ConstantZ (_, _)-> false
  | AdditionZ (_, _, _, _) -> false
  | MultiplicationZ (_, _, _, _) -> true

let as_multiplicationz (z : z_t) =
  match z with
  | PInputZ (_, _) -> witness
  | SInputZ (_, _) -> witness
  | ConstantZ (_, _) -> witness
  | AdditionZ (_, _, _, _) -> witness
  | MultiplicationZ (gid, zi, zl, zr) -> (gid, zi, zl, zr)

type z_t1 = z_t

type z'_t = (Z.t) * (Z.t)

let rec get_c (z: z_t) : Z.t =
  match z with
  | PInputZ (wid, zi) -> zi.c2
  | SInputZ (wid, zi) -> zi.c2
  | ConstantZ (gid, zi) -> zi.c2
  | AdditionZ (gid, zi, zl, zr) -> zi.c2
  | MultiplicationZ (gid, zi, zl, zr) -> zi.c2
  
let rec gen_z (u: ui_t array) (gg2: gates_t) (xp: (Z.t) array) (xs: (Z.t) array) :
  z_t =
  match gg2 with
  | PInput wid ->
    (let b1 = let result = nth def_ui1 u wid in result.b in
     let w1 = eval_gates gg2 xp xs in
     (PInputZ (wid, { m = fsub  w1 b1; m' = Z.zero ; c2 = Z.zero  }) ))
  | SInput wid ->
    (let b1 = let result = nth def_ui1 u wid in result.b in
     let w1 = eval_gates gg2 xp xs in
     (SInputZ (wid, { m = fsub  w1 b1; m' = Z.zero ; c2 = Z.zero  }) ))
  | Constant (gid,
    c3) ->
    (let b1 = let result = nth def_ui1 u gid in result.b in
     let w1 = eval_gates gg2 xp xs in
     (ConstantZ (gid, { m = fsub  w1 b1; m' = Z.zero ; c2 = Z.zero  }) ))
  | Addition (gid,
    wl,
    wr) ->
    (let b1 = let result = nth def_ui1 u gid in result.b in
     let w1 = eval_gates gg2 xp xs in
     (AdditionZ (gid, { m = fsub  w1 b1; m' = Z.zero ; c2 = Z.zero  }, gen_z u wl xp xs, gen_z u wr xp xs) ))
  | Multiplication (gid,
    l,
    r) ->
    (let wl = eval_gates l xp xs in let wr = eval_gates r xp xs in
     let w1 = fmul  wl wr in let ui = nth def_ui1 u gid in let ai = ui.a in
     let ai' = ui.a' in let bi = ui.b in let bi' = ui.b' in
     let ul = nth def_ui1 u (get_gid l) in let al = ul.a in
     let ur = nth def_ui1 u (get_gid r) in let ar = ur.a in
     let (zl1) =
     gen_z u l xp xs in
     let (zr1) =
     gen_z u r xp xs in
     let c3 = fsub  (fsub  (fadd  (fmul  al wr) (fmul  ar wl)) ai) bi' in
     (MultiplicationZ (gid,
      { m = fsub  w1 bi; m' = fsub  (fmul  al ar) ai'; c2 = c3 },
      zl1,
      zr1)))

let get_a (u: ui_t array) (gg2: gates_t) : Z.t =
  let gid = get_gid gg2 in let ui = nth def_ui u gid in ui.a

let get_a1 (u: ui_t array) (gg2: gates_t) : Z.t = get_a u gg2

type commitment_t = z_t * ((Z.t))

let add_final_mul (c3: topology_t * gates_t) : topology_t * gates_t =
  let (topo2,
  gg2) =
  c3 in
  let max_wire = get_gid gg2 in
  let ntopo =
    { npinputs = topo2.npinputs; nsinputs = topo2.nsinputs; ngates =
      Z.add topo2.ngates (Z.of_string "2"); noutputs = topo2.noutputs } in
  let ngg =
    Multiplication (Z.add max_wire Z.one, Constant (max_wire, Z.one ), gg2) in
  (ntopo, ngg)

let commit (r: ui_t array)
           (x: ((Z.t) array) * ((topology_t * gates_t) * ((Z.t) array))) :
  z_t * ((Z.t)) =
  let (w1,
  st1) =
  x in
  let (c3,
  inst2) =
  st1 in
  let c4 = add_final_mul c3 in
  let (topo3,
  gg3) =
  c4 in
  let (z) =
  gen_z r gg3 inst2 w1 in
  let z' = let result = get_a1 r gg3 in (result) in (z, z')

type fi_t = {
  e: Z.t;
  e': Z.t;
  e'': Z.t;
  }

type fi_t1 = fi_t

type f_t =
  | PInputF of fi_t
  | SInputF of fi_t
  | ConstantF of fi_t
  | AdditionF of fi_t * f_t * f_t
  | MultiplicationF of fi_t * f_t * f_t

type f_t1 = f_t

let rec get_fi (f: f_t) : fi_t =
  match f with
  | PInputF fi -> fi
  | SInputF fi -> fi
  | ConstantF fi -> fi
  | AdditionF (fi, fl, fr) -> fi
  | MultiplicationF (fi, fl, fr) -> fi

let get_fi1 (f: f_t) : fi_t = get_fi f

let get_e (f: f_t) : Z.t = (get_fi f).e

let get_e1 (f: f_t) : Z.t = get_e f

let bad = PInputF { e = Z.zero ; e' = Z.zero ; e'' = Z.zero  }

let rec is_pinput (g: gates_t) : bool =
  match g with
  | PInput _ -> true
  | SInput _ -> false
  | Constant (_, _) -> false
  | Addition (_, _, _) -> false
  | Multiplication (_, _, _) -> false

let rec as_pinput (g: gates_t) =
  match g with
  | PInput wid -> wid
  | SInput _ -> ((Obj.magic None))
  | Constant (_, _) -> ((Obj.magic None))
  | Addition (_, _, _) -> ((Obj.magic None))
  | Multiplication (_, _, _) -> ((Obj.magic None))

let rec is_sinput (g: gates_t) : bool =
  match g with
  | PInput _ -> false
  | SInput _ -> true
  | Constant (_, _) -> false
  | Addition (_, _, _) -> false
  | Multiplication (_, _, _) -> false

let rec as_sinput (g: gates_t) =
  match g with
  | PInput _ -> ((Obj.magic None))
  | SInput wid -> wid 
  | Constant (_, _) -> ((Obj.magic None))
  | Addition (_, _, _) -> ((Obj.magic None))
  | Multiplication (_, _, _) -> ((Obj.magic None))

let rec is_constant (g: gates_t) : bool =
  match g with
  | PInput _ -> false
  | SInput _ -> false
  | Constant (_, _) -> true
  | Addition (_, _, _) -> false
  | Multiplication (_, _, _) -> false

let rec as_constant (g: gates_t) =
  match g with
  | PInput _ -> ((Obj.magic None))
  | SInput _ -> ((Obj.magic None)) 
  | Constant (gid, c) -> (gid, c)
  | Addition (_, _, _) -> ((Obj.magic None))
  | Multiplication (_, _, _) -> ((Obj.magic None))

let rec is_addition (g: gates_t) : bool =
  match g with
  | PInput _ -> false
  | SInput _ -> false
  | Constant (_, _) -> false
  | Addition (_, _, _) -> true
  | Multiplication (_, _, _) -> false

let rec as_addition (g: gates_t) : (Z.t) * gates_t * gates_t =
  match g with
  | PInput _ -> ((Obj.magic None))
  | SInput _ -> ((Obj.magic None))
  | Constant (_, _) -> ((Obj.magic None))
  | Addition (gid, wl, wr) -> (gid, wl, wr)
  | Multiplication (_, _, _)  -> ((Obj.magic None))

let rec is_multiplication (g: gates_t) : bool =
  match g with
  | PInput _ -> false
  | SInput _ -> false
  | Constant (_, _) -> false
  | Addition (_, _, _) -> false
  | Multiplication (_, _, _) -> true

let rec as_multiplication (g: gates_t) : (Z.t) * gates_t * gates_t =
  match g with
  | PInput _ -> ((Obj.magic None))
  | SInput _ -> ((Obj.magic None))
  | Constant (_, _) -> ((Obj.magic None))
  | Addition (_, _, _) -> ((Obj.magic None))
  | Multiplication (gid, wl, wr) -> (gid, wl, wr)

let rec gen_f (r: verifier_rand_t) (z1: z_t) : f_t =
  match z1 with
  | PInputZ (wid,
    zi) ->
      let m1 = zi.m in
      let v1 = let o = nth def_yi1 r.y wid in o.v in
      PInputF { e = fadd  v1 m1; e' = Z.zero ; e'' = Z.zero  }
  | SInputZ (wid,
    zi) ->
      let m1 = zi.m in
      let v1 = let o = nth def_yi1 r.y wid in o.v in
      SInputF { e = fadd  v1 m1; e' = Z.zero ; e'' = Z.zero  }
  | ConstantZ (gid,
    zi) ->
      let m1 = zi.m in
      let v1 = let o = nth def_yi1 r.y gid in o.v in
      ConstantF { e = fadd  v1 m1; e' = Z.zero ; e'' = Z.zero  }
  | AdditionZ (gid,
    zi,
    zl2,
    zr2) ->
      let m1 = zi.m in
      let v1 = let o = nth def_yi1 r.y gid in o.v in
      AdditionF ({ e = fadd  v1 m1; e' = Z.zero ; e'' = Z.zero  },
      gen_f r zl2,
        gen_f r zr2)
  | MultiplicationZ (gid,
    zi,
    zl2,
    zr2) ->
      let (
      fl1) =
      gen_f r zl2 in
      let (
      fr1) =
      gen_f r zr2 in
      let m1 = zi.m in
      let m'1 = zi.m' in
      let alpha1 = r.alpha in
      let y1 = nth def_yi1 r.y gid in
      let v1 = y1.v in
      let v'1 = y1.v' in
      let el = get_e1 fl1 in
      let er = get_e1 fr1 in
      let e1 = fadd  v1 m1 in
      let e'1 = fadd  v'1 (fmul  alpha1 m'1) in
        MultiplicationF ({ e = e1; e' = e'1; e'' =
                           fsub  (fsub  (fmul  el er) e1) (fmul  alpha1 e'1) },
        fl1,
        fr1)

let rec get_m (z1: z_t) : Z.t =
  match z1 with
  | PInputZ (_, zi) -> zi.m
  | SInputZ (_, zi) -> zi.m
  | ConstantZ (_, zi) -> zi.m
  | AdditionZ (_, zi, _, _) -> zi.m
  | MultiplicationZ (_, zi, _, _) -> zi.m

let get_m1 (z1: z_t) : Z.t = get_m z1

let rec get_gid_z (z1: z_t) : Z.t =
  match z1 with
  | PInputZ (wid, _) -> wid
  | SInputZ (wid, _) -> wid
  | ConstantZ (gid, _) -> gid
  | AdditionZ (gid, _, _, _) -> gid
  | MultiplicationZ (gid, _, _, _) -> gid

let get_gid_z1 (z1: z_t) : Z.t = get_gid_z z1

let rec is_multiplication_z (z1: z_t) : bool =
  match z1 with
  | PInputZ (wid, _) -> false
  | SInputZ (wid, _) -> false
  | ConstantZ (gid, _) -> false
  | AdditionZ (gid, _, _, _) -> false
  | MultiplicationZ (gid, _, _, _) -> true

let is_multiplication_z1 (z1: z_t) : bool = is_multiplication_z z1

let rec check_m (z1: z_t) (r: verifier_rand_t) (n: Z.t) : bool =
  match z1 with
  | PInputZ (wid,
    zi) ->
    (let o =
       let o1 = let o2 = let o3 = nth def_yi r.y wid in o3.v in fadd  o2 in
       o1 (get_m z1) in
     logical_equality o (fmul  r.alpha n))
  | SInputZ (wid,
    zi) ->
    (let o =
       let o1 = let o2 = let o3 = nth def_yi r.y wid in o3.v in fadd  o2 in
       o1 (get_m z1) in
     logical_equality o (fmul  r.alpha n))
  | ConstantZ (gid,
    zi) ->
    (let o =
       let o1 = let o2 = let o3 = nth def_yi r.y gid in o3.v in fadd  o2 in
       o1 (get_m z1) in
     logical_equality o (fmul  r.alpha n))
  | AdditionZ (gid, zi, zl2, zr2) -> logical_equality (get_m z1) (Z.zero )
  | MultiplicationZ (gid,
    zi,
    zl2,
    zr2) ->
    (let o =
       let o1 = let o2 = let o3 = nth def_yi r.y gid in o3.v in fadd  o2 in
       o1 (get_m z1) in
     logical_equality o (fmul  r.alpha n))

let check_m1 (z1: z_t) (r: verifier_rand_t) (n: Z.t) : bool = check_m z1 r n

let snd : type a b. (a * b) ->  b = fun p -> let (a1, b1) = p in b1

let rec batch_check (f : f_t) (z : z_t) (alpha : Z.t) : 
  bool = 
  match f with
  | PInputF _ -> is_pinputz z
  | SInputF _ -> is_sinputz z
  | ConstantF _ -> is_constantz z
  | AdditionF (_, fl, fr) -> 
      if (is_additionz z) 
      then
        boolean_and 
        (batch_check fl (trd4 (as_additionz z)) alpha) 
        (batch_check fr (frt4 (as_additionz z)) alpha)
      else 
      false
  | MultiplicationF (fi, fl, fr) -> 
      if (is_multiplicationz z) 
      then
        boolean_and 
        (boolean_and 
          (fi.e'' = fmul alpha (snd4 (as_multiplicationz z)).c2)  (batch_check fl (trd4 (as_multiplicationz z)) alpha))
          (batch_check fr (frt4 (as_multiplicationz z)) alpha)
      else 
      false

let rec valid_z_gates (z : z_t) (gg : gates_t) : 
  bool =
  match z with
  | PInputZ (wid, _) -> 
    if is_pinput gg 
    then 
    logical_equality (as_pinput gg) (wid) 
    else 
    false
  | SInputZ (wid, _) -> 
    if is_sinput gg 
    then 
    logical_equality (as_sinput gg) (wid) 
    else 
    false    
  | ConstantZ (gid, _) -> 
    if is_constant gg 
    then 
    logical_equality (fst (as_constant gg)) (gid) 
    else 
    false    
  | AdditionZ (gid, _, zl, zr) -> 
    if is_addition gg 
    then
      let (gid', wl, wr) = as_addition gg in
      boolean_and (boolean_and (logical_equality (gid) (gid')) (valid_z_gates zl wl)) (valid_z_gates zr wr)
    else 
    false
  | MultiplicationZ (gid, _, zl, zr) ->
    if is_multiplication gg 
    then
      let (gid', wl, wr) = as_multiplication gg in
      boolean_and (boolean_and (logical_equality (gid) (gid')) (valid_z_gates zl wl)) (valid_z_gates zr wr)
    else 
    false

let valid_z (z : z_t) (c : topology_t * gates_t) : 
  bool =
  valid_z_gates z (snd c)

let prove (r: verifier_rand_t) (x: (topology_t * gates_t) * ((Z.t) array))
          (c6: z_t * ((Z.t))) : bool =
  let (z1,
  z') =
  c6 in
  let (circ,
  inst3) =
  x in
  if valid_circuit circ 
  then
    let circ = add_final_mul circ in
    let n = z' in
    if boolean_and (valid_z z1 circ) (boolean_not (logical_equality n (Z.zero )))
    then
      let f = gen_f r z1 in
      if batch_check f z1 r.alpha
      then
        logical_equality (get_e1 f) (fmul n r.alpha)
      else
      false
    else
    false
  else
  false

type trace_t = z_t * ((Z.t))

let protocol (r: (ui_t array) * verifier_rand_t)
             (x:
             (((Z.t) array) * ((topology_t * gates_t) * ((Z.t) array))) *
             ((topology_t * gates_t) * ((Z.t) array))) :
  (z_t * ((Z.t))) * (unit * (bool)) =
  let (r_p,
  r_v) =
  r in
  let (x_p,
  x_v) =
  x in
  let c6 = commit r_p x_p in let b3 = prove r_v x_v c6 in (c6, ((), b3))
