let snd (p: 'a * 'b) : 'b = let (_, y1) = p in y1

let pred1 (c: 'a) (x1: 'a) : bool = x1 = c
let predC = fun (p : 'a -> bool) x -> not (p x)

let fst (p: 'a * 'b) : 'a = let (x1, _) = p in x1

let fst3 (x : ('a* 'b* 'c) ) =
    let (x1,x2,x3) = x in x1
let snd3 (x : ('a * 'b* 'c) ) =
    let (x1,x2,x3) = x in x2
let thr3 (x : ('a* 'b* 'c) ) =
     let (x1,x2,x3) = x in x3
     
let witness : 'a = (Obj.magic Option.None)