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

type statement_t = (topology_t * gates_t) * ((Z.t) array)

let rec nth : type a. a -> (a array) -> (Z.t) ->  a =
  fun x xs n -> Array.get xs (Z.to_int n)

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

let boolean_and (b1: bool) (b'1: bool) : bool = b1 && b'1

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

let boolean_not (b1: bool) : bool = not b1

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

type z_t1 = z_t

type z'_t = (Z.t) * (Z.t)

let rec get_c (z: z_t) : Z.t =
  match z with
  | PInputZ (wid, zi) -> zi.c2
  | SInputZ (wid, zi) -> zi.c2
  | ConstantZ (gid, zi) -> zi.c2
  | AdditionZ (gid, zi, zl, zr) -> zi.c2
  | MultiplicationZ (gid, zi, zl, zr) -> zi.c2

let rec get_gid (g: gates_t) : Z.t =
  match g with
  | PInput wid -> wid
  | SInput wid -> wid
  | Constant (gid, c3) -> gid
  | Addition (gid, wl, wr) -> gid
  | Multiplication (gid, wl, wr) -> gid
  
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
    (let (zl) = gen_z u wl xp xs in
     let (zr) =
     gen_z u wr xp xs in
     (AdditionZ (gid, { m = Z.zero ; m' = Z.zero ; c2 = Z.zero  }, zl, zr)))
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

let rec is_sinput (g: gates_t) : bool =
  match g with
  | PInput _ -> false
  | SInput _ -> true
  | Constant (_, _) -> false
  | Addition (_, _, _) -> false
  | Multiplication (_, _, _) -> false

let rec is_constant (g: gates_t) : bool =
  match g with
  | PInput _ -> false
  | SInput _ -> false
  | Constant (_, _) -> true
  | Addition (_, _, _) -> false
  | Multiplication (_, _, _) -> false

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
  | Multiplication (_, _, _) -> ((Obj.magic None))

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

let rec gen_f (r: verifier_rand_t) (gg4: gates_t) (z1: z_t) : (bool) * f_t =
  match z1 with
  | PInputZ (wid,
    zi) ->
    if is_pinput gg4
    then 
      let m1 = zi.m in
      let v1 = let o = nth def_yi1 r.y wid in o.v in
      (true, PInputF { e = fadd  v1 m1; e' = Z.zero ; e'' = Z.zero  })
    else (false, bad)
  | SInputZ (wid,
    zi) ->
    if is_sinput gg4
    then 
      let m1 = zi.m in
      let v1 = let o = nth def_yi1 r.y wid in o.v in
      (true, SInputF { e = fadd  v1 m1; e' = Z.zero ; e'' = Z.zero  }) 
    else (false, bad)
  | ConstantZ (gid,
    zi) ->
    if is_constant gg4
    then 
      let m1 = zi.m in
      let v1 = let o = nth def_yi1 r.y gid in o.v in
      (true, ConstantF { e = fadd  v1 m1; e' = Z.zero ; e'' = Z.zero  }) 
    else (false, bad)
  | AdditionZ (gid,
    zi,
    zl2,
    zr2) ->
    if is_addition gg4
    then 
      let (gid1,
      wl,
      wr) =
      as_addition gg4 in
      let (bl,
      fl) =
      gen_f r wl zl2 in
      let (br,
      fr) =
      gen_f r wr zr2 in
      if boolean_and bl br
      then
        (true,
        AdditionF ({ e = fadd  (get_e1 fl) (get_e1 fr); e' = Z.zero ; e'' =
                     Z.zero  },
        fl,
        fr)) 
      else (false, bad) 
    else (false, bad)
  | MultiplicationZ (gid,
    zi,
    zl2,
    zr2) ->
    if is_multiplication gg4
    then 
      let (gid2,
      wl1,
      wr1) =
      as_multiplication gg4 in
      let (bl1,
      fl1) =
      gen_f r wl1 zl2 in
      let (br1,
      fr1) =
      gen_f r wr1 zr2 in
      let m1 = zi.m in
      let m'1 = zi.m' in
      let alpha1 = r.alpha in
      let y1 = nth def_yi1 r.y gid2 in
      let v1 = y1.v in
      let v'1 = y1.v' in
      let el = get_e1 fl1 in
      let er = get_e1 fr1 in
      let e1 = fadd  v1 m1 in
      let e'1 = fadd  v'1 (fmul  alpha1 m'1) in
      if boolean_and bl1 br1
      then
        (true,
        MultiplicationF ({ e = e1; e' = e'1; e'' =
                           fsub  (fsub  (fmul  el er) e1) (fmul  alpha1 e'1) },
        fl1,
        fr1)) 
      else (false, bad) 
    else (false, bad)

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

let prove (r: verifier_rand_t) (x: (topology_t * gates_t) * ((Z.t) array))
          (c6: z_t * ((Z.t))) : bool =
  let (z1,
  z') =
  c6 in
  let (circ,
  inst3) =
  x in
  let (topo4,
  gg4) =
  circ in
  let (b2,
  f) =
  gen_f r (snd (add_final_mul (topo4, gg4))) z1 in
  let (n) =
  z' in
  boolean_and (boolean_not (logical_equality n (Z.zero ))) b2 && logical_equality 
                                                                 (get_e1 f)
                                                                 (fmul  n 
                                                                 r.alpha)

type trace_t = z_t * ((Z.t) * (Z.t))

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

