require import List Int.

require import Array5 Array6 Array9 Array10.

op array5_zip3 (xs:'a Array5.t) (ys:'b Array5.t) (zs:'c Array5.t) : ('a*'b*'c) Array5.t =
  Array5.init (fun i => (xs.[i],ys.[i],zs.[i]) ).

lemma array5_to_list_init (f:int->'a) :
  Array5.to_list (Array5.init f) = mkseq f 5.
  apply (eq_from_nth witness) => />. rewrite !size_mkseq => />i. rewrite !size_to_list => />.
  move => i Hi1 Hi2. rewrite initE andabP andaP => />. rewrite nth_mkseq => />. qed.

lemma array5_to_list (xs:'a Array5.t) :
  to_list xs = [xs.[0];xs.[1];xs.[2];xs.[3];xs.[4]].
  apply/(eq_from_nth witness) => />. rewrite size_to_list => /> /#. rewrite size_to_list => /#.  qed.

lemma array9_to_list (xs:'a Array9.t) :
  to_list xs = [xs.[0];xs.[1];xs.[2];xs.[3];xs.[4];xs.[5];xs.[6];xs.[7];xs.[8]].
  apply/(eq_from_nth witness) => />. rewrite size_to_list => /> /#. rewrite size_to_list => /#.  qed.

lemma array10_to_list (xs:'a Array10.t) :
  to_list xs = [xs.[0];xs.[1];xs.[2];xs.[3];xs.[4];xs.[5];xs.[6];xs.[7];xs.[8];xs.[9]].
  apply/(eq_from_nth witness) => />. rewrite size_to_list => /> /#. rewrite size_to_list => /#. qed.
