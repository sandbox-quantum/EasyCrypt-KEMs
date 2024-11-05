require import AllCore.
require PublicKeyEncryption.

clone include PublicKeyEncryption.
clone include OW.

print Adv_INDCPA.

module R (A : Adv_OWCPA) : Adv_INDCPA = {
  var m0, m1 : ptxt_t
  var pk' : pk_t
  
  proc choose(pk : pk_t) : ptxt_t * ptxt_t = {
    pk' <- pk;
    
    m0 <$ dptxtm pk;
    m1 <$ dptxtm pk;
    
    return (m0, m1);
  }
  
  proc distinguish(c : ctxt_t) : bool = {
    var b : bool;
    var m : ptxt_t;
    
    m <@ A.find(pk', c);
    
    return m = m1;
  }
}.



section.

declare module S <: Scheme {-R}.
declare module A <: Adv_OWCPA {-R, -S}.


lemma test &m :
  Pr[OW_CPA(S, A).main() @ &m : res]
  =
  Pr[IND_CPA(S, R(A)).main() @ &m : res].
proof.
byequiv=> //.
proc.
inline{2} 5; inline{2} 2.
wp.
call (: true).
wp.
call (: true).
swap{2} 7 -6.
seq 0 1 : #pre.
rnd{2}. skip => //.
case (b{2} = false).
wp.
rnd{2}.
rnd.
wp.
call (: true).
skip => />. progress. admit. 
search (<=>) (=).
rewrite eq_iff.
split =>  [->|]. admit. 


smt().

wp.
rnd.
rnd{2}.  
wp.
call (: true).
skip => />. progress.
admit. smt().
have t: (m0 <> pL). admit. 
rewrite (: b{2}).
smt().
simplify.
case (result_R1 = pL).
smt(). 
