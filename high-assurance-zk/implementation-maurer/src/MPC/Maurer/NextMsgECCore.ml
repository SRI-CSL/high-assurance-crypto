open NextMsgECInt
open NextMsgECPervasive
open NextMsgECList
open NextMsgECLogic
module Aux = struct
    let constfun (b : 'b) (_ : 'a) : 'b =
                                            b
    let fst3 (x : ('a * ('b * 'c))) : 'a =
                                             (fst x)
    let snd3 (x : ('a * ('b * 'c))) : 'b =
                                             (fst (snd x))
    let thr3 (x : ('a * ('b * 'c))) : 'c =
                                             (snd (snd x))
    type ('a) array1 = 'a
    type ('a) array2 = ('a * 'a)
    type ('a) array3 = ('a * ('a * 'a))
    type ('a) array4 = ('a * ('a * ('a * 'a)))
    type ('a) array5 = ('a * ('a * ('a * ('a * 'a))))
    type ('a) array6 = ('a * ('a * ('a * ('a * ('a * 'a)))))
    let nth0_3 (x : ('a) array3) : 'a =
                                          (fst3 x)
    let nth1_3 (x : ('a) array3) : 'a =
                                          (snd3 x)
    let nth2_3 (x : ('a) array3) : 'a =
                                          (thr3 x)
    let nth0_4 (x : ('a) array4) : 'a =
                                          (fst3 x)
    let nth1_4 (x : ('a) array4) : 'a =
                                          (nth0_3 (snd x))
    let nth2_4 (x : ('a) array4) : 'a =
                                          (nth1_3 (snd x))
    let nth3_4 (x : ('a) array4) : 'a =
                                          (nth2_3 (snd x))
    let nth0_5 (x : ('a) array5) : 'a =
                                          (fst3 x)
    let nth1_5 (x : ('a) array5) : 'a =
                                          (nth0_4 (snd x))
    let nth2_5 (x : ('a) array5) : 'a =
                                          (nth1_4 (snd x))
    let nth3_5 (x : ('a) array5) : 'a =
                                          (nth2_4 (snd x))
    let nth4_5 (x : ('a) array5) : 'a =
                                          (nth3_4 (snd x))
    let nth0_6 (x : ('a) array6) : 'a =
                                          (fst3 x)
    let nth1_6 (x : ('a) array6) : 'a =
                                          (nth0_5 (snd x))
    let nth2_6 (x : ('a) array6) : 'a =
                                          (nth1_5 (snd x))
    let nth3_6 (x : ('a) array6) : 'a =
                                          (nth2_5 (snd x))
    let nth4_6 (x : ('a) array6) : 'a =
                                          (nth3_5 (snd x))
    let nth5_6 (x : ('a) array6) : 'a =
                                          (nth4_5 (snd x))
    let array1 (x1 : 'a) : 'a =
                                  x1
    let array2 (x1 : 'a) (x2 : 'a) : ('a * 'a) =
                                                   (x1 , x2)
    let array3 (x1 : 'a) (x2 : 'a) (x3 : 'a) : ('a * ('a * 'a)) =
                                                                    (x1 , (x2 , x3))
    let array4 (x1 : 'a) (x2 : 'a) (x3 : 'a) (x4 : 'a) : ('a * ('a * ('a * 'a))) =
                                                                                     (x1 , (x2 , (x3 , x4)))
    let array5 (x1 : 'a) (x2 : 'a) (x3 : 'a) (x4 : 'a) (x5 : 'a) : ('a * ('a * ('a * ('a * 'a)))) =
                                                                                                      (x1 , (x2 , (x3 , (x4 , x5))))
    let array6 (x1 : 'a) (x2 : 'a) (x3 : 'a) (x4 : 'a) (x5 : 'a) (x6 : 'a) : ('a * ('a * ('a * ('a * ('a * 'a))))) =
                                                                                                                       (x1 , (x2 , (x3 , (x4 , (x5 , x6)))))
    let init_array5 (f : (Pervasive.int -> 'a)) : ('a * ('a * ('a * ('a * 'a)))) =
                                                                                     (array5 (f (Pervasive.mk_int 0)) (f (Pervasive.mk_int 1)) (f (Pervasive.mk_int 2)) (f (Pervasive.mk_int 3)) (f (Pervasive.mk_int 4)))
    let set_array2 (xs : ('a) array2) (i : Pervasive.int) (x : 'a) : ('a) array2 =
                                                                                     if (Pervasive.eq i (Pervasive.mk_int 0)) then (x , (snd xs)) else if (Pervasive.eq i (Pervasive.mk_int 1)) then ((fst xs) , x) else xs
    let set_array3 (xs : ('a) array3) (i : Pervasive.int) (x : 'a) : ('a * ('a) array2) =
                                                                                            if (Pervasive.eq i (Pervasive.mk_int 0)) then (x , (snd xs)) else ((nth0_3 xs) , (set_array2 (snd xs) (Int.minus i (Pervasive.mk_int 1)) x))
    let set_array4 (xs : ('a) array4) (i : Pervasive.int) (x : 'a) : ('a * ('a * ('a) array2)) =
                                                                                                   if (Pervasive.eq i (Pervasive.mk_int 0)) then (x , (snd xs)) else ((nth0_4 xs) , (set_array3 (snd xs) (Int.minus i (Pervasive.mk_int 1)) x))
    let set_array5 (xs : ('a) array5) (i : Pervasive.int) (x : 'a) : ('a * ('a * ('a * ('a) array2))) =
                                                                                                          if (Pervasive.eq i (Pervasive.mk_int 0)) then (x , (snd xs)) else ((nth0_5 xs) , (set_array4 (snd xs) (Int.minus i (Pervasive.mk_int 1)) x))
    let list_to_array1 (xs : ('a) List.list) : 'a =
                                                      (array1 (List.nth (Pervasive.witness) xs (Pervasive.mk_int 0)))
    let list_to_array2 (xs : ('a) List.list) : ('a * 'a) =
                                                             (array2 (List.nth (Pervasive.witness) xs (Pervasive.mk_int 0)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 1)))
    let list_to_array3 (xs : ('a) List.list) : ('a * ('a * 'a)) =
                                                                    (array3 (List.nth (Pervasive.witness) xs (Pervasive.mk_int 0)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 1)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 2)))
    let list_to_array4 (xs : ('a) List.list) : ('a * ('a * ('a * 'a))) =
                                                                           (array4 (List.nth (Pervasive.witness) xs (Pervasive.mk_int 0)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 1)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 2)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 3)))
    let list_to_array5 (xs : ('a) List.list) : ('a * ('a * ('a * ('a * 'a)))) =
                                                                                  (array5 (List.nth (Pervasive.witness) xs (Pervasive.mk_int 0)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 1)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 2)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 3)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 4)))
    let list_to_array6 (xs : ('a) List.list) : ('a * ('a * ('a * ('a * ('a * 'a))))) =
                                                                                         (array6 (List.nth (Pervasive.witness) xs (Pervasive.mk_int 0)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 1)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 2)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 3)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 4)) (List.nth (Pervasive.witness) xs (Pervasive.mk_int 5)))
    let nth_array1 (x : ('a) array1) (i : Pervasive.int) : ('a) array1 =
                                                                           if (Pervasive.eq i (Pervasive.mk_int 0)) then x else (Pervasive.witness)
    let nth_array2 (x : ('a) array2) (i : Pervasive.int) : 'a =
                                                                  if (Pervasive.eq i (Pervasive.mk_int 0)) then (fst x) else if (Pervasive.eq i (Pervasive.mk_int 1)) then (snd x) else (Pervasive.witness)
    let nth_array3 (x : ('a) array3) (i : Pervasive.int) : 'a =
                                                                  if (Pervasive.eq i (Pervasive.mk_int 0)) then (nth0_3 x) else if (Pervasive.eq i (Pervasive.mk_int 1)) then (nth1_3 x) else if (Pervasive.eq i (Pervasive.mk_int 2)) then (nth2_3 x) else (Pervasive.witness)
    let nth_array4 (x : ('a) array4) (i : Pervasive.int) : 'a =
                                                                  if (Pervasive.eq i (Pervasive.mk_int 0)) then (nth0_4 x) else if (Pervasive.eq i (Pervasive.mk_int 1)) then (nth1_4 x) else if (Pervasive.eq i (Pervasive.mk_int 2)) then (nth2_4 x) else if (Pervasive.eq i (Pervasive.mk_int 3)) then (nth3_4 x) else (Pervasive.witness)
    let nth_array5 (x : ('a) array5) (i : Pervasive.int) : 'a =
                                                                  if (Pervasive.eq i (Pervasive.mk_int 0)) then (nth0_5 x) else if (Pervasive.eq i (Pervasive.mk_int 1)) then (nth1_5 x) else if (Pervasive.eq i (Pervasive.mk_int 2)) then (nth2_5 x) else if (Pervasive.eq i (Pervasive.mk_int 3)) then (nth3_5 x) else if (Pervasive.eq i (Pervasive.mk_int 4)) then (nth4_5 x) else (Pervasive.witness)
    let nth_array6 (x : ('a) array6) (i : Pervasive.int) : 'a =
                                                                  if (Pervasive.eq i (Pervasive.mk_int 0)) then (nth0_6 x) else if (Pervasive.eq i (Pervasive.mk_int 1)) then (nth1_6 x) else if (Pervasive.eq i (Pervasive.mk_int 2)) then (nth2_6 x) else if (Pervasive.eq i (Pervasive.mk_int 3)) then (nth3_6 x) else if (Pervasive.eq i (Pervasive.mk_int 4)) then (nth4_6 x) else if (Pervasive.eq i (Pervasive.mk_int 5)) then (nth5_6 x) else (Pervasive.witness)
    let prod (f : ('a -> 'c)) (g : ('b -> 'd)) (ab : ('a * 'b)) : ('c * 'd) =
                                                                                ((f (fst ab)) , (g (snd ab)))
    let osame (p : ('a -> ('b -> Pervasive.bool))) (x : ('a) Logic.option) (y : ('b) Logic.option) : Pervasive.bool =
                                                                                                                        begin match x with
                                                                                                                        | (Logic.None) -> (Logic.is_none y)
                                                                                                                        | (Logic.Some a) -> (Logic.oapp (p a) (Pervasive._false) y)
                                                                                                                        end
    let ojoin (f : ('a -> ('a -> 'a))) (x : ('a) Logic.option) (y : ('a) Logic.option) : ('a) Logic.option =
                                                                                                               begin match x with
                                                                                                               | (Logic.None) -> y
                                                                                                               | (Logic.Some a) -> (Logic.oapp (fun (b : 'a) -> (Logic.Some (f a b))) (Logic.Some a) y)
                                                                                                               end
    let omerge (f : ('a -> ('b -> 'c))) (x : ('a) Logic.option) (y : ('b) Logic.option) : ('c) Logic.option =
                                                                                                                begin match x with
                                                                                                                | (Logic.None) -> (Logic.None)
                                                                                                                | (Logic.Some a) -> (Logic.oapp (fun (b : 'b) -> (Logic.Some (f a b))) (Logic.None) y)
                                                                                                                end
    let ozip (x : ('a) Logic.option) (y : ('b) Logic.option) : (('a * 'b)) Logic.option =
                                                                                            (Logic.oapp (fun (a : 'a) -> (Logic.oapp (fun (b : 'b) -> (Logic.Some (a , b))) (Logic.None) y)) (Logic.None) x)
    let ozip3 (x : ('a) Logic.option) (y : ('b) Logic.option) (z : ('c) Logic.option) : (('a * ('b * 'c))) Logic.option =
                                                                                                                            (ozip x (ozip y z))
    type ('a, 'b) either = | L of 'a
                           | R of 'b
    let either (f : ('a -> 'c)) (g : ('b -> 'c)) (e : ('a, 'b) either) : 'c =
                                                                                begin match e with
                                                                                | (L a) -> (f a)
                                                                                | (R b) -> (g b)
                                                                                end
    let unL (e : ('a, 'b) either) : 'a =
                                           begin match e with
                                           | (L a) -> a
                                           | (R b) -> (Pervasive.witness)
                                           end
    let unR (e : ('a, 'b) either) : 'b =
                                           begin match e with
                                           | (L a) -> (Pervasive.witness)
                                           | (R b) -> b
                                           end
    let isL (e : ('a, 'b) either) : Pervasive.bool =
                                                       begin match e with
                                                       | (L a) -> (Pervasive._true)
                                                       | (R b) -> (Pervasive._false)
                                                       end
    let isR (e : ('a, 'b) either) : Pervasive.bool =
                                                       begin match e with
                                                       | (L a) -> (Pervasive._false)
                                                       | (R b) -> (Pervasive._true)
                                                       end
    let eq_either (f : ('a -> ('a -> Pervasive.bool))) (g : ('b -> ('b -> Pervasive.bool))) (e1 : ('a, 'b) either) (e2 : ('a, 'b) either) : Pervasive.bool =
                                                                                                                                                               begin match e1 with
                                                                                                                                                               | (L x) -> (either (f x) (constfun (Pervasive._false)) e2)
                                                                                                                                                               | (R x) -> (either (constfun (Pervasive._false)) (g x) e2)
                                                                                                                                                               end
    let uncurry (f : ('a -> ('b -> 'c))) (xy : ('a * 'b)) : 'c =
                                                                   (f (fst xy) (snd xy))
    let uncurry3 (f : ('a -> ('b -> ('c -> 'd)))) (xyz : ('a * ('b * 'c))) : 'd =
                                                                                    (f (fst3 xyz) (snd3 xyz) (thr3 xyz))
end
