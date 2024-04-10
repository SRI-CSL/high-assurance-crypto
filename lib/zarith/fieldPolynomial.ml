open EcList
open EcPrimeField
open EcOption

type monomial = {
    coef: t;
    expo: Z.t;
  }

let mzero = { coef = zero; expo = zero }

let meval (x1: Z.t) (m: monomial) : Z.t =
  fmul (m.coef) (Z.powm x1 (m.expo) !q)

let rec eval (x1: Z.t) (p: monomial list) : Z.t =
  begin match p with
  | Nil -> Z.zero
  | Cons (m, pqt) -> fadd (meval x1 m) (eval x1 pqt)
  end

let madd (m1: monomial) (m2: monomial) : monomial =
  { coef = (fadd (m1.coef) (m2.coef)); expo = (m1.expo) }

let rec add (p1: monomial list) (p2: monomial list) : monomial list =
  begin match (p1, p2) with
  | (Nil, Nil) -> Nil
  | (Cons (m1, p1qt), Nil) -> p1
  | (Nil, Cons (m2, p2qt)) -> p2
  | (Cons (m1, p1qt), Cons (m2, p2qt)) ->
     if (m1.expo) = (m2.expo) then begin
         Cons ((madd m1 m2), (add p1qt p2qt)) end
     else
       begin
         if Z.lt (m1.expo) (m2.expo) then begin Cons (m2, (add p1 p2qt)) end
         else
           begin
             Cons (m1, (add p1qt p2)) end end
  end

let rec mpadd (m: monomial) (p: monomial list) : monomial list =
  begin match p with
  | Nil -> Cons (m, Nil)
  | Cons (mqt, pqt) ->
     if (m.expo) = (mqt.expo) then begin Cons ((madd m mqt), pqt) end
     else
       begin
         if Z.lt (mqt.expo) (m.expo) then begin Cons (m, p) end
         else
           begin
             Cons (mqt, (mpadd m pqt)) end end
  end

let mmul (m1: monomial) (m2: monomial) : monomial =
  { coef = (fmul (m1.coef) (m2.coef)); expo =
                                              (Z.add (m1.expo) (m2.expo)) }

let rec mpmul (m: monomial) (p: monomial list) : monomial list =
  begin match p with
  | Nil -> Nil
  | Cons (mqt, pqt) -> mpadd (mmul m mqt) (mpmul m pqt)
  end

let mone  : monomial = { coef = Z.one; expo = Z.zero }

let one  : monomial list = Cons (mone, Nil)

let rec mul (p1: monomial list) (p2: monomial list) : monomial list =
  begin match p1 with
  | Nil -> Nil
  | Cons (m, p1qt) -> add (mpmul m p2) (mul p1qt p2)
  end

let mumin (m: monomial) : monomial =
  { coef = fumin m.coef ; expo = m.expo }

let rec umin (p: monomial list) : monomial list =
  begin match p with
  | Nil -> Nil
  | Cons (m, pqt) -> Cons ((mumin m), (umin pqt))
  end

let rec basis (x2: Z.t) (xs: (Z.t) list) : monomial list =
  begin match xs with
  | Nil -> one
  | Cons (xqt, xsqt) ->
     if x2 = xqt then begin basis x2 xsqt end
     else
       begin
         mul (Cons (({ coef = (fdiv Z.one (fsub x2 xqt)); expo =
                                                                     Z.one }),
                    (Cons (({ coef = (fdiv (fumin xqt) (fsub x2 xqt));
                              expo = Z.zero }), Nil)))) (basis x2 xsqt) end
  end

let interpolateqt (xs: (Z.t) list) (pm: ((Z.t) * (Z.t)) list) : monomial list
  =
  foldr (fun (x2: Z.t) (poly: monomial list) ->
      add (mpmul ({ coef = (odflt Z.zero (assoc pm x2)); expo = Z.zero })
             (basis x2 xs)) poly) Nil xs

let interpolate_poly (pm: ((Z.t) * (Z.t)) list) : monomial list =
  interpolateqt (map fst pm) pm

let rec basis_loop (x : Z.t) (xmx : Z.t) (xm : Z.t list) : Z.t list =
  match xm with
  | Nil -> Nil
  | Cons (y,ys) ->
     if not (Z.equal y xmx) then
       Cons ((fdiv (fsub x y) (fsub xmx y)), basis_loop x xmx ys)
     else basis_loop x xmx ys

let basis (x : Z.t) (xmx : Z.t) (xm : Z.t list) =
  foldr (fun (x : Z.t) (y : Z.t) -> fmul x y) Z.one (basis_loop x xmx xm)
  
let rec interpolate_loop (x : Z.t) (xm : Z.t list) (pm : (Z.t * Z.t) list) =
  match pm with
  | Nil -> Nil
  | Cons (y, ys) ->
     Cons ((fmul (basis x (fst y) xm) (snd y)), interpolate_loop x xm ys)

let interpolate (x : Z.t) (pm : (Z.t * Z.t) list) =
  let xm = map fst pm in
  let bs = interpolate_loop x xm pm in
  foldr (fun (x : Z.t) (y : Z.t) -> fadd x y) Z.zero bs

let rec update (p : monomial list) (e : Z.t) (x : t) : monomial list =
  begin match p with
  | Nil -> Nil
  | Cons (m, ms) ->
     if m.expo = e then Cons ({ coef = x ; expo = e }, ms)
     else Cons (m, update ms e x)
  end

let rec dpolynomial' (i : Z.t) (d : Z.t) (p : monomial list) : monomial list =
  if Z.gt i d then p
  else
    let coef = dt () in
    if coef = Z.zero then dpolynomial' i d p
    else dpolynomial' (Z.add i Z.one) d (Cons ({ coef = coef ; expo = i}, p))
    
let dpolynomial : Z.t -> monomial list =
  fun n -> dpolynomial' Z.zero n Nil

let monomial_to_string m = Z.to_string m.coef ^ "x^" ^ Z.to_string m.expo

let rec polynomial_to_string p =
  match p with
  | Nil -> ""
  | Cons (m, Nil) -> monomial_to_string m
  | Cons (m, p) -> monomial_to_string m ^ " + " ^ polynomial_to_string p