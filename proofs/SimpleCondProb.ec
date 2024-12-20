require import AllCore Distr List.
require import Finite.
require (*--*) StdBigop.
(*---*) import StdBigop.Bigreal.BRA.


abstract theory Generic.

type in_t.
type out_t.
type aux_t.

op din : in_t distr.

module type Provided = {
  proc main(x : in_t, aux : aux_t) : out_t
}.

module Sampler (P : Provided) = {
  var x : in_t
  
  proc main(aux : aux_t) : out_t = {
    var y : out_t;
    
    x <$ din;
    y <@ P.main(x, aux);
    
    return y;
  }
}.


section.

declare module P <: Provided {-Sampler}.
declare op prop : aux_t -> in_t -> glob P -> out_t -> bool.

lemma EqPr_SamplerConj_ProvidedCond &m (a : aux_t) (v : in_t) :
  Pr[Sampler(P).main(a) @ &m : Sampler.x = v /\ prop a (Sampler.x) (glob P) res] 
  = 
  (mu1 din v) *  Pr[P.main(v, a) @ &m : prop a v (glob P) res].
proof.
byphoare (: glob P = (glob P){m} /\ arg = a ==> _ ) => //.
pose prPCond := Pr[P.main(v, a) @ &m : prop a v (glob P) res].
proc.
seq 1 : (Sampler.x = v) (mu1 din v) prPCond _ 0%r (glob P = (glob P){m} /\ aux = a) => //; 1,2: by rnd.
+ call (: glob P = (glob P){m} /\ arg = (v, a) ==> prop a v (glob P) res) => //.
  rewrite /prPCond; bypr=> /> &m' eqGl ->.
  by byequiv => //; proc true.
by hoare; call(: true); skip => />. 
qed.

lemma EqPr_SamplerConj_ProvidedCond_FinBig &m (a : aux_t) :
  is_finite (support din) 
  => Pr[Sampler(P).main(a) @ &m : prop a (Sampler.x) (glob P) res] 
     = 
     big predT (fun (v : in_t) => (mu1 din v) * Pr[P.main(v, a) @ &m : prop a v (glob P) res]) 
               (to_seq (support din)).
proof.
move=> finsup; rewrite Pr[mu_split (Sampler.x \in to_seq (support din))].
have -> /=:
  Pr[Sampler(P).main(a) @ &m : prop a Sampler.x (glob P) res /\ ! (Sampler.x \in to_seq (support din))]
  =
  0%r.
+ byphoare => //=.
  hoare => /=.
  proc.
  call (: true).
  rnd; skip => /> x.
  by rewrite (mem_to_seq _ _ finsup) => ->.
elim: (to_seq (support din)) (uniq_to_seq (support din)) => /= [| x l ih /= [nxinl uql]].
+ by rewrite big_nil; byphoare.
rewrite big_cons /predT /= -/predT.
by rewrite andb_orr Pr[mu_disjoint] 1:/# ih 1:// -EqPr_SamplerConj_ProvidedCond andbC.
qed.

lemma EqPr_SamplerConj_ProvidedCond_UniBig &m (a : aux_t) :
  is_uniform din 
  => Pr[Sampler(P).main(a) @ &m : prop a (Sampler.x) (glob P) res] 
     = 
     weight din / (size (to_seq (support din)))%r
     * big predT (fun (v : in_t) => Pr[P.main(v, a) @ &m : prop a v (glob P) res]) (to_seq (support din)).
proof.
move=> ^ /uniform_finite finsup unidin.
rewrite mulr_sumr /= (EqPr_SamplerConj_ProvidedCond_FinBig &m a finsup).
apply eq_big_seq => x /=.
by rewrite (mem_to_seq _ _ finsup) (mu1_uni _ _ unidin) => ->.
qed.

end section.

end Generic.


theory Indistinguishability.
require import DBool.

clone import Generic as IND with
  type in_t <- bool,
  type out_t <- bool,
  type aux_t <- unit,
  op din <- {0,1}.

section.

declare module P <: Provided {-Sampler}.
declare axiom P_main_ll : islossless P.main.

lemma RelPr_IndSampler_IndProvided &m :
  2%r * Pr[Sampler(P).main() @ &m : res = Sampler.x] - 1%r
  =
  Pr[P.main(true, tt) @ &m : res] - Pr[P.main(false, tt) @ &m : res].
proof.
rewrite (EqPr_SamplerConj_ProvidedCond_UniBig P (fun a v g b => b = v) &m tt dbool_uni) /=.
rewrite (: support {0,1} = predT); 1: by rewrite fun_ext => b; rewrite supp_dbool.
rewrite -Support.card_size_to_seq dboolE -(eq_big_perm predT _ _ _  Support.perm_eq_enum_to_seq). 
rewrite 2!big_cons big_nil /predT /= -/predT.
rewrite -[_ = false]negbK Pr[mu_not] (: Pr[P.main(false, tt) @ &m : true] = 1%r) 2:/#.
by byphoare P_main_ll.
qed.

lemma Rel_Ind_Formalizations &m :
  2%r * `| Pr[Sampler(P).main() @ &m : res = Sampler.x] - 1%r/2%r |
  =
  `| Pr[P.main(false, tt) @ &m : res] - Pr[P.main(true, tt) @ &m : res] |.
proof. smt(RelPr_IndSampler_IndProvided). qed.

end section.

end Indistinguishability.
