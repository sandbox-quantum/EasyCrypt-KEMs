(* Test *)
module SNM_CCA_Split(S : Scheme, O : Oracles_CCA2i, A : Adv_SNMCCA) = {
  proc rest(b : bool, o : bool) = {
    var pk : pk_t;
    var sk : sk_t;
    var k : key_t;
    var k' : key_t;
    var c : ctxt_t;
    var rel : key_t -> key_t option list -> bool;
    var cl : ctxt_t list;
    var ko : key_t option;
    var kol : key_t option list;
    
    (pk, sk) <@ S.keygen();
    (k, c) <@ S.encaps(pk);
    k' <$ (dkeym pk)%NM;
    O.init(sk, c);
    
    (rel, cl) <@ A(O).find(pk, c, if o then (k', k) else (k, k'));
    kol <- [];
    while (size kol < size cl){
      ko <@ S.decaps(sk, nth witness cl (size kol));
      kol <- rcons kol ko;
    }
    
    return ! (c \in cl) /\ rel (if b then k' else k) kol;
  }
  
  proc main(b : bool) : bool = {
    var o, r : bool;
    

    o <$ {0,1};
    r <@ rest(b, o);
    
    return r;
  }
}.

module (R_SNMCCA_INDCCAP (A : Adv_INDCCA) : Adv_SNMCCA) (O : Oracles_CCA) = {
  proc find(pk : pk_t, c : ctxt_t, kk : key_t * key_t) : (key_t -> key_t option list -> bool) * ctxt_t list = {
    var b' : bool;
    
    b' <@ A(O).distinguish(pk, kk.`1, c);
    
    return (fun k kl, k = if b' then kk.`2 else kk.`1, []);    
  }
}.


lemma test (S <: Scheme) (O <: Oracles_CCA2i{-S}) (A <: Adv_INDCCA{-S, -O}) &m :
  IND.dkeym = NM.dkeym =>
  Pr[SNM_CCA_Split(S, O, R_SNMCCA_INDCCAP(A)).main(false) @ &m : res]
  =
  1%r / 2%r * Pr[IND_CCA_P(S, O, A).main(false) @ &m : !res]
  +
  1%r / 2%r * Pr[IND_CCA_P(S, O, A).main(true) @ &m : res].
proof. admit. qed.


lemma test2 (S <: Scheme) (O <: Oracles_CCA2i{-S}) (A <: Adv_INDCCA{-S, -O}) &m :
  IND.dkeym = NM.dkeym =>
  Pr[SNM_CCA_Split(S, O, R_SNMCCA_INDCCAP(A)).main(true) @ &m : res]
  =
  1%r / 2%r * Pr[IND_CCA_P(S, O, A).main(false) @ &m : res]
  +
  1%r / 2%r * Pr[IND_CCA_P(S, O, A).main(true) @ &m : !res].
proof. admit. qed.



lemma test3 (S <: Scheme) (O <: Oracles_CCA2i{-S}) (A <: Adv_INDCCA{-S, -O}) &m :
  IND.dkeym = NM.dkeym =>
  Pr[SNM_CCA_Split(S, O, R_SNMCCA_INDCCAP(A)).main(false) @ &m : res]
  -
  Pr[SNM_CCA_Split(S, O, R_SNMCCA_INDCCAP(A)).main(true) @ &m : res]  
  =
  Pr[IND_CCA_P(S, O, A).main(true) @ &m : res]
  -
  Pr[IND_CCA_P(S, O, A).main(false) @ &m : res].
proof.
move=> t.
move: (test S O A &m t) (test2 S O A &m t).
rewrite Pr[mu_not] Pr[mu_not].
have ->:
  Pr[IND_CCA_P(S, O, A).main(false) @ &m : true]
  =
  1%r.
+ admit.
have ->:
  Pr[IND_CCA_P(S, O, A).main(true) @ &m : true]
  =
  1%r.
+ admit.
smt().
qed. 
