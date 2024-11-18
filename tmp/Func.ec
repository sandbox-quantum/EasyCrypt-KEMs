require import AllCore.


module type X = {
  proc m() : unit
}.

module type NonFunc = {
  proc p() : unit
}.

module type Func (S : X) = {
  proc p() : unit
}.

module NOF (S : X, O : NonFunc) = {
  proc main() : unit = {
    S.m();
    O.p();
  }
}.

module YESF (S : X, O : Func) = {
  proc main() : unit = {
    S.m();
    O(S).p();
  }
}.

lemma FooNOF (S <: X) (O <: NonFunc{-S}) :
  equiv[NOF(S, O).main ~ NOF(S, O).main : ={glob S, glob O} ==> ={glob S}].
proof. proc. call (: true). by call (: true). qed.

lemma FooYESF (S <: X) (O <: Func{-S}) :
  equiv[YESF(S, O).main ~ YESF(S, O).main : ={glob S, glob O} ==> ={glob S}].
proof. proc. call (: ={glob S}); 1: by sim. by call (: true). qed.


module NF (S : X) : NonFunc = {
  var t : int
  proc p() = {
    S.m();
  }
}.

module (YF : Func) (S : X) = {
  var t : int
  proc p() = {
    S.m();
  }
}.

module St : X = {
  var  t : int
  proc m() : unit = {
     var s <- t;
  }
}.

module NF2 (S : X) : NonFunc = {
  var t : int
  proc p() = {
    t <- St.t;
    S.m();
  }
}.

lemma FooInst : true.
proof.
move: (FooYESF St NF2).
