require import AllCore Int List.
require import Aux AuxList.
require import NextMsgISet.
require import SmtMap AuxSmtMap.

(* A dynamic size map *)
theory IMap.

  import ISet.

  type 'a imap = (int,'a) fmap.
  op get  (xs:'a imap) (i:int) : 'a option = (xs).[i].
  op set (xs:'a imap) (i:int) (x:'a) : 'a imap = ((xs).[i <- x]).
  op rem (xs:'a imap) (i:int) : 'a imap = (SmtMap.rem (xs) i).
  op size (xs:'a imap) : int = FSet.card (fdom (xs)).

  op ofset (f:int -> 'a) (xs:iset) : 'a imap = (AuxSmtMap.ofset f (xs)).
  op empty :'a imap = SmtMap.empty.
  op imap (f:int -> 'a -> 'b) (xs:'a imap) : 'b imap = (SmtMap.map f (xs)).
  op map (f:'a -> 'b) (xs:'a imap) : 'b imap =  (AuxSmtMap.fmap f (xs)).
  op ofassoc (xs:(int*'a) list) : 'a imap = (SmtMap.ofassoc xs).

  op zip (xs : 'b1 imap) (ys : 'b2 imap) : ('b1*'b2) imap = (fzip (xs) (ys)).
  op merge (f:'b1 -> 'b2 -> 'b3) (xs : ('b1) imap) (ys : ('b2) imap) : ('b3) imap = (AuxSmtMap.fmerge f (xs) (ys)).
  op all (f:int -> 'b -> bool) (xs:('b) imap) : bool = fall f (xs).

  op dom (xs:'a imap) : iset = (SmtMap.fdom (xs)).

  op redom (cr:iset) (xs:('b) imap) : ('b) imap =
    ofset (fun i => oget (get xs i)) cr.

end IMap.
