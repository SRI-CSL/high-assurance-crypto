require import AllCore Int List.
require import Aux AuxList.
require import FSet AuxFSet.

(* A dynamic size set *)
theory ISet.

  type iset = int fset.

  op oflist : int list -> iset = FSet.oflist.

  op elems : iset -> int list = FSet.elems.

  op mem (x:int) (xs:iset) : bool = x \in (xs).

  op subset (xs ys : iset) : bool = (xs) \subset (ys).

  op card : iset -> int = FSet.card.

  op union (xs ys: iset) : iset = (xs) `|` (ys).

  op intersect (xs ys : iset) : iset = (xs) `&` (ys).

  op all (f:int -> bool) (xs:iset) : bool = fsetall f (xs).

  op set0 : iset = fset0.

  op set1 (x:int) : iset = (fset1 x).

  op iset (n:int) : iset = (AuxFSet.iset n).

  abbrev add (s:iset) (x:int) : iset = union s (set1 x).
  
  op equal (s1 s2 : iset) : bool = (s1 = s2).

end ISet.

  

