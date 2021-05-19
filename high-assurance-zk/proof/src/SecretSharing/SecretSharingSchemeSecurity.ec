require import DBool List.

from SecretSharing require import ASecretSharingScheme.

from General require import ListExt.

theory SecretSharingSchemeSecurity.

  clone import SecretSharingScheme.

  type aux_t.

  module type Rand_t = {
    proc gen(aux : aux_t) : rand_t
  }.

  module type Distinguisher_t = {
    proc choose(aux : aux_t) : pid_t list
    proc guess(s : secret_t, ss : shares_t) : bool
  }.

  module type Evaluator_t = {
    proc share(aux : aux_t, r : rand_t, s : secret_t, cr : pid_t list) : shares_t
  }.

  module Game(D : Distinguisher_t, R : Rand_t, E : Evaluator_t) = {
    proc main(aux : aux_t, s : secret_t) : bool = {
      var r, b', ss, cr;

      cr <@ D.choose(aux);
      r <@ R.gen(aux);
      if (valid_rand r) {
        ss <@ E.share(aux,r,s,cr);
        b' <@ D.guess(s,ss);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  module RealEvaluator = {
    proc share(aux : aux_t, r : rand_t, s : secret_t, cr : pid_t list) : shares_t = {
      var ss, ssc;

      ss <- share r s;
      ssc <- map (fun pid => (pid, oget (assoc ss pid))) cr;

      return ssc;
    }
  }.

  module type Simulator_t = {
    proc simm(aux : aux_t, cr : pid_t list) : shares_t
  }.

  module IdealEvaluator (S : Simulator_t) = {
    proc share(aux : aux_t, r : rand_t, s : secret_t, cr : pid_t list) : shares_t = {
      var ssc;

      ssc <- S.simm(aux,cr);

      return ssc;
    }
  }.

  module GameReal (D : Distinguisher_t) (R : Rand_t) = Game(D,R,RealEvaluator).
  module GameIdeal (D : Distinguisher_t) (R : Rand_t) (S : Simulator_t) = Game(D,R,IdealEvaluator(S)).

end SecretSharingSchemeSecurity.

(*theory ListSecretSharingSchemeSecurity.

  clone import ListSecretSharingScheme.

  type data_t.

  module type Rand_t = {
    proc gen(x : data_t) : rand_t
  }.

  module type Adversary_t = {
    proc choose() : (secret_t * secret_t * pid_t * pid_t * data_t) option
    proc guess(ss : share_t * share_t) : bool option
  }.

  module Game (R : Rand_t) (A : Adversary_t) = {
    proc game(b : bool) : bool = {
      var r, s0, s1, i, j, ss, b', query, ob',d;

      query <@ A.choose();
      if (query <> None) {
        (s0,s1,i,j,d) <- oget query;
        r <@ R.gen(d);
          if (valid_secret s0 /\ valid_secret s1 /\ i <> j /\ valid_rand r s0 /\ valid_rand r s1) {
            ss <- share r (b ? s1 : s0);
            ob' <@ A.guess(get_party_share i ss, get_party_share j ss);
            if (ob' <> None) { b' <- oget ob'; }
            else { b' <${0,1}; }
          } else { b' <${0,1}; }
        } else { b' <${0,1}; }

      return (b = b');
    }
    
    proc main() : bool = {
      var b, adv;
      
      b <$ {0,1};
      adv <@ game(b);
      return adv;
    }
  }.

end ListSecretSharingSchemeSecurity.
*)
