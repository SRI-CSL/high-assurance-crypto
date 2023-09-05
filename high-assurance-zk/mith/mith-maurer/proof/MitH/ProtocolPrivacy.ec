require import DBool List AuxList Aux Int.

require import AProtocol.
require import AProtocolFunctionality.

theory Privacy.

  clone import Protocol as P.
  import F.

  type aux_t.
  type env_input_t.
  
  module type Rand_t = {
    proc gen(c : circuit_t, cr : pid_t list, aux : aux_t) : rands_t
  }.

  module type Distinguisher_t = {
    proc choose(c : circuit_t, x : env_input_t, aux : aux_t) : inputs_t * pid_t list
    proc guess(vsc : views_t) : bool
  }.

  module type Evaluator_t = {
    proc eval(c : circuit_t, xs : inputs_t, cr : pid_t list, rs : rands_t) : views_t
  }.

  op valid_corrupted_set (cr : pid_t list) : bool = 
    size cr = t /\ uniq cr /\ (forall pid, pid \in cr => pid \in pid_set).
    
  (* Condition on inputs but used to express output validity for MitH ZeroKnowledge *)
  op restricted_inputs (c:circuit_t) (xs:inputs_t) : bool.

  module Game(D : Distinguisher_t, R : Rand_t, E : Evaluator_t) = {
    proc main(c : circuit_t, x : env_input_t, aux : aux_t) : bool = {
      var r, b', vsc, xs, cr;

      (xs,cr) <@ D.choose(c,x,aux);
      r <@ R.gen(c,cr,aux);
      if (valid_inputs c xs /\ restricted_inputs c xs /\ valid_rands c r /\ valid_corrupted_set cr) {
        vsc <@ E.eval(c, xs, cr, r);
        b' <@ D.guess(vsc);
      } else { b' <${0,1}; } 
      return b';
    }
    proc main_c(c : circuit_t, xs, cr,aux) : bool = {
      var r, b', vsc;

      r <@ R.gen(c,cr,aux);
      if (valid_inputs c xs /\ restricted_inputs c xs /\ valid_rands c r /\ valid_corrupted_set cr) {
        vsc <@ E.eval(c, xs, cr, r);
        b' <@ D.guess(vsc);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  module RealEvaluator = {
    proc eval(c : circuit_t, xs : inputs_t, cr : pid_t list, rs : rands_t) : views_t = {
      var tr, y, vsc;

      (tr, y) <- protocol c rs xs;
      vsc <- map (fun pid => (pid, (input pid xs, (rand pid rs, trace pid tr)))) cr;

      return vsc;
    }
  }.

  module type Simulator_t = {
    proc simm(c : circuit_t, xs : inputs_t, rs : rands_t, cr : pid_t list, y : F.outputs_t) : views_t
  }.

  module IdealEvaluator (S : Simulator_t) = {
    proc eval(c : circuit_t, xs : inputs_t, cr : pid_t list, rs : rands_t) : views_t = {
      var xsc, vsc, ys;

      xsc <- extract_inputs xs cr;
      ys <- f c xs;
      ys <- map (fun pid => (pid, oget (assoc ys pid))) cr;
      vsc <- S.simm(c, xsc, rs, cr, ys);

      return vsc;
    }
  }.

  module GameReal (D : Distinguisher_t) (R : Rand_t) = Game(D,R,RealEvaluator).
  module GameIdeal (D : Distinguisher_t) (R : Rand_t) (S : Simulator_t) = Game(D,R,IdealEvaluator(S)).

  section Proofs.
  
  declare module D : Distinguisher_t.
  declare module R : Rand_t {D}.
  declare module S : Simulator_t {D,R}.

  (* privacy property for concrete randomness generator and concrete simulator *)
  axiom privacy_c :
    equiv [GameReal(D,R).main_c ~ GameIdeal(D,R,S).main_c : ={glob D,glob R,glob S,c,aux,xs,cr} /\ valid_circuit c{1} ==> ={res} ]. 

  lemma privacy :
    equiv [GameReal(D,R).main ~ GameIdeal(D,R,S).main : ={glob D,glob R,glob S,c,aux,x} /\ valid_circuit c{1} ==> ={res} ]. 
    proc. simplify. 
    seq 1 1 : ( valid_circuit c{1} /\ ={glob D,glob R,glob S,c,xs,cr,aux} ).
    call (_: true ) => />*. auto => />*. 
    transitivity{1}
      { b' <@ GameReal(D,R).main_c(c,xs,cr,aux); }
      ( valid_circuit c{1} /\ ={glob D,glob R,glob S,c,xs,cr,aux} ==> ={b'} )
      ( valid_circuit c{1} /\ ={glob D,glob R,glob S,c,xs,cr,aux} ==> ={b'} ).
      progress. exists (glob D){2} (glob R){2} (glob S){2} aux{2} c{2} cr{2} xs{2} => />*. 
      progress. 
    inline *. sp. 
    seq 1 1 : (#pre /\ r{1}=r0{2}). 
    call (_: true ) => |>. auto.
    if. progress. 
    wp. sp.
    call (_: true ) => |>. auto => |>.
    move => &1 &2. rewrite (prod_id (protocol c{2} r0{2} xs{2})) => |>. 
    wp. auto => |>. 
    transitivity{2}
      { b' <@ GameIdeal(D,R,S).main_c(c,xs,cr,aux); }
      ( valid_circuit c{1} /\ ={glob D,glob R,glob S,c,xs,cr,aux} ==> ={b'} )
      ( valid_circuit c{1} /\ ={glob D,glob R,glob S,c,xs,cr,aux} ==> ={b'} ).
      progress. exists (glob D){2} (glob R){2} (glob S){2} aux{2} c{2} cr{2} xs{2} => />*. 
      progress. 
    call privacy_c => |>. auto. 
    inline *. sp. 
    seq 1 1 : (#pre /\ r0{1}=r{2}). 
    call (_: true ) => |>. auto.
    if. progress. 
    wp. sp.
    seq 1 1 : (#pre /\ vsc1{1}=vsc0{2}). 
    call (_: true ) => |>. auto => |>.
    sp. 
    call (_: true ) => |>. auto => |>.
    wp. auto => |>. qed.

  end section Proofs.

end Privacy.

theory BoolPrivacy.

  clone import Privacy as Priv.
  clone import BoolProtocol as BoolP with
    theory P <- Priv.P.

  clone include Privacy with
    theory P <- BoolP,
    op restricted_inputs c xs = Priv.restricted_inputs c xs /\ all snd (F.f c xs),
    type aux_t = Priv.aux_t,
    type env_input_t = Priv.env_input_t.

  section BPrivacy.
  
  declare module D : Priv.Distinguisher_t.
  declare module R : Priv.Rand_t {D}.
  declare module S : Priv.Simulator_t {D,R}.

  axiom privacy_c :
    equiv [Priv.GameReal(D,R).main_c ~ Priv.GameIdeal(D,R,S).main_c : ={glob D,glob R,glob S,c,aux,xs,cr} /\ P.F.valid_circuit c{1} ==> ={res} ]. 

  (* simulator for the specific case when the output is true, as required for MitH ZeroKnowledge proof *)
  local module BSimulator : Simulator_t = {
    proc simm(c : F.circuit_t, xs : F.inputs_t, rs : rands_t, cr : F.pid_t list, y : F.outputs_t) : views_t = {
      var v;
      v <@ S.simm(c,xs,rs,cr,map (fun i => (i,true_output)) cr);
      return v;
    }
  }.

  lemma valid_corrupted_set_conv cr :
    BoolPrivacy.valid_corrupted_set cr = Priv.valid_corrupted_set cr.
    rewrite /valid_corrupted_set => />. qed.

  local lemma bprivacy_c :
    equiv [GameReal(D,R).main_c ~ GameIdeal(D,R,BSimulator).main_c : ={glob D,glob R,glob S,c,aux,xs,cr} /\ P.F.valid_circuit c{1}==> ={res} ]. 
    proc. 
    case (BoolPrivacy.restricted_inputs c{1} xs{1}).
    transitivity{1}
      { b' <@ Priv.GameReal(D,R).main_c(c,xs,cr,aux); }
      ( P.F.valid_circuit c{1} /\ BoolPrivacy.restricted_inputs c{1} xs{1} /\ ={glob D,glob R,glob S,c,xs,cr,aux} ==> ={b'} )
      ( P.F.valid_circuit c{1} /\ BoolPrivacy.restricted_inputs c{1} xs{1} /\ ={glob D,glob R,glob S,c,xs,cr,aux} ==> ={b'} ).
      progress. exists (glob D){2} (glob R){2} (glob S){2} aux{2} c{2} cr{2} xs{2} => />*. 
      progress. 
    inline *. wp. sp. 
    seq 1 1 : (#pre /\ r{1}=r0{2}). 
    call (_: true ) => |>. auto. 
    if. move => &1 &2. move => H. split. move :H. rewrite /valid_inputs /restricted_inputs valid_corrupted_set_conv => |>. move :H. rewrite /valid_inputs /restricted_inputs valid_corrupted_set_conv => |>.
    wp. sp.
    call (_: true ) => |>. auto => |>.
    move => &1 &2. rewrite /protocol /prod /idfun => |>. rewrite (prod_id (P.protocol c{2} r0{2} xs{2})) => |>. 
    auto => |>. 
    transitivity{2}
      { b' <@ Priv.GameIdeal(D,R,S).main_c(c,xs,cr,aux); }
      ( P.F.valid_circuit c{1} /\ BoolPrivacy.restricted_inputs c{1} xs{1} /\ ={glob D,glob R,glob S,c,xs,cr,aux} ==> ={b'} )
      ( P.F.valid_circuit c{1} /\ BoolPrivacy.restricted_inputs c{1} xs{1} /\ ={glob D,glob R,glob S,c,xs,cr,aux} ==> ={b'} ).
      progress. exists (glob D){2} (glob R){2} (glob S){2} aux{2} c{2} cr{2} xs{2} => />*. 
      progress. 
    call privacy_c => |>. auto. 
    inline *. sp.
    seq 1 1 : (#pre /\ r0{1}=r{2}). 
    call (_: true ) => |>. auto. 
    if. move => &1 &2. move => H. split. move :H. rewrite /valid_inputs /restricted_inputs valid_corrupted_set_conv => |>. move :H. rewrite /valid_inputs /restricted_inputs valid_corrupted_set_conv => |>.
    wp. sp.
    seq 1 1 : (#pre /\ vsc1{1}=v{2}). 
    call (_: true ) => |>. auto => |>.
    move => &2. rewrite /restricted_inputs allP => |>H H0 H1 H2 H3 H4. apply (eq_from_nth witness) => |>. rewrite !size_map => |>. move => i. move :H4. rewrite /valid_corrupted_set => |>H8 H9 H10. rewrite !size_map H8 => |>Hi1 Hi2. rewrite !(nth_map witness) => |>. rewrite H8 => |>. rewrite H8 => |>.
    have : unzip1 (snd (P.protocol c{2} r{2} xs{2})) = F.pid_set /\ unzip1 (fst (P.protocol c{2} r{2} xs{2})) = F.pid_set. rewrite P.correct_domain => |>. move => |> H5 H6.
    have : size (P.F.f c{2} xs{2}) = F.n. rewrite -(P.correct c{2} r{2} xs{2}) => |>. have : size (unzip1 (P.protocol c{2} r{2} xs{2}).`2) = size F.pid_set. rewrite H5 => |>. rewrite size_map F.pid_set_size => |>. move => H7.
    have : unzip1 (P.F.f c{2} xs{2}) = F.pid_set. rewrite -(P.correct c{2} r{2} xs{2}) => |>. move => H13.
    have : size (F.f c{2} xs{2}) = F.n. rewrite /f => |>. rewrite size_map => |>. move => H11.
    have : (nth witness cr{2} i) \in F.pid_set. rewrite H10 => |>. rewrite nth_in => |>. rewrite H8 => |>. rewrite in_nth => |>j. rewrite F.pid_set_size => |> Hj1 Hj2 H12. rewrite H12 => |>. rewrite -(unzip1_eq_nth (P.F.f c{2} xs{2}) F.pid_set) => |>. rewrite H7 => |>. rewrite assoc_nth_some => |>. rewrite H7 => |>. rewrite H13 P.F.pid_set_uniq => |>.
    have : (nth witness (F.f c{2} xs{2}) j).`2. rewrite H1 => |>. rewrite nth_in => |>. rewrite H11 => |>. rewrite /f => |>. rewrite !(nth_map witness) => |>. rewrite H7 => |>.  
    sp. 
    call (_: true ) => |>. auto => |>.
    wp. auto => |>. 
    seq 1 1 : (#pre /\ r{1}=r{2}). 
    call (_: true ) => |>. auto. 
    if. progress. progress.
    conseq (_ : false ==> _ ). progress. smt(). auto => />. progress.
    auto => |>. qed.

  end section BPrivacy.

end BoolPrivacy.
