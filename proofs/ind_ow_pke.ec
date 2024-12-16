require import AllCore Distr RealFLub.

require PublicKeyEncryption.





clone import PublicKeyEncryption as PKE.


op pmax_pk (dpm : pk_t -> ptxt_t distr) =  
  flub (fun pk => p_max (dpm pk)).



clone import OW.

module R_IND_OW (A : Adv_OWCPA) : Adv_INDCPA = {
  var pk' : pk_t
  var p, p' : ptxt_t
  
  proc choose(pk : pk_t) : ptxt_t * ptxt_t = {
    pk' <- pk;
    
    p <$ dptxtm pk;
    p' <$ dptxtm pk;
    
    return (p, p');  
  }
  
  proc distinguish(c : ctxt_t) : bool = {
    var pinv : ptxt_t;
    
    pinv <@ A.find(pk', c);
    
    return pinv = p'; 
  }
}.


section.

declare module S <: Scheme{-R_IND_OW}.

declare module A <: Adv_OWCPA {-R_IND_OW, -S}.

declare axiom dptxtm_ll pk : is_lossless (dptxtm pk).  


local module OW_CPA_V = { 
  var p0, p1 : ptxt_t
  proc main() : bool = {
    var pk : pk_t;
    var sk : sk_t;
    var p' : ptxt_t;
    var c : ctxt_t;
    
    (pk, sk) <@ S.keygen();
    p0 <$ dptxtm pk;
    p1 <$ dptxtm pk;
    c <@ S.enc(pk, p0);
    p' <@ A.find(pk, c);
    
    return p' = p0;
  }
}.

local equiv test : 
OW_CPA(S, A).main ~ OW_CPA_V.main : ={glob S, glob A} ==> ={res}.  
proof.
proc.
call (: true).
call (: true).
rnd{2}; rnd; call (: true); skip => />; smt(dptxtm_ll). 
qed.


local lemma testpr &m :
  Pr[OW_CPA(S, A).main() @ &m : res]
  <=
  Pr[IND_CPA(S, R_IND_OW(A)).main() @ &m : res]
  +
  pmax_pk dptxtm.
proof.
rewrite (: Pr[OW_CPA(S, A).main() @ &m : res] = Pr[OW_CPA_V.main() @ &m : res]).
+ byequiv test => //.
rewrite Pr[mu_split OW_CPA_V.p0 <> OW_CPA_V.p1] /= StdOrder.RealOrder.ler_add.
+ byequiv => //.
  proc.
  inline{2} *.
  wp; call (: true); wp; call (: true).
  swap{2} 7 -6; seq 1 2 : (={glob S, glob A, pk, sk}); 1: by call (: true); rnd{2}. 
  by case (b{2}); 1: swap{2} 3 1; wp; rnd; rnd; wp; skip => />. 
rewrite (StdOrder.RealOrder.ler_trans Pr[OW_CPA_V.main() @ &m : OW_CPA_V.p0 = OW_CPA_V.p1]).
+ byequiv (: _ ==> ={OW_CPA_V.p0, OW_CPA_V.p1}) => //.
  proc.
  by sim.
byphoare => //.
proc.
seq 3 : (#post) (pmax_pk dptxtm) 1%r _ 0%r => //.
seq 2 : true 1%r (pmax_pk dptxtm) 0%r _ => //.
rnd; skip => /> &m'.
rewrite /pmax_pk.
apply (StdOrder.RealOrder.ler_trans (p_max (dptxtm pk{m'}))); 1: smt(pmax_upper_bound).
pose F pk' := p_max (dptxtm pk').
apply (flub_upper_bound F).
rewrite /F /has_fub; exists 1%r; rewrite /is_fub => pk'.
apply pmax_le1.
hoare.
conseq />. 
by call (: true); call (: true). 
qed.

end section.
