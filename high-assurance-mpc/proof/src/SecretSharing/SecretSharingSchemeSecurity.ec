require import DBool List.

from SecretSharing require import ASecretSharingScheme.

from General require import ListExt.

theory SecretSharingSchemeSecurity.

  clone import SecretSharingScheme.

  module type Rand_t = {
    proc gen() : rand_t
  }.

  module type Distinguisher_t = {
    proc guess(s : secret_t, ss : (pid_t * share_t) list) : bool
  }.

  module type Simulator_t = {
    proc simm(cr : pid_t list) : (pid_t * share_t) list
  }.

  module Game (R : Rand_t) (D : Distinguisher_t) (S : Simulator_t) = {
    proc game(s : secret_t, cr : pid_t list, b : bool) : bool = {
      var r, b', ss, ss0, ss1;

      r <@ R.gen();
      if (valid_rand r) {
        ss <- share r s;
        ss0 <- filter (fun x => fst x \in cr) ss;
        ss1 <@ S.simm(cr);
        b' <@ D.guess(s, if b then ss1 else ss0);
      } else { b' <${0,1}; }

      return (b = b');
    }
    
    proc main(s : secret_t, cr : pid_t list) : bool = {
      var b, adv;
      
      b <$ {0,1};
      adv <@ game(s,cr,b);
      return adv;
    }
  }.

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
