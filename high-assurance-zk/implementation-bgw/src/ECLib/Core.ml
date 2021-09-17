let snd (p: 'a * 'b) : 'b = let (_, y1) = p in y1

let pred1 (c: 'a) (x1: 'a) : bool = x1 = c

let fst (p: 'a * 'b) : 'a = let (x1, _) = p in x1
