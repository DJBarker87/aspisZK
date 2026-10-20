import FinishDotSourceABI
import CurrentFinishEquality
import FinishCandidateDotSuccess
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishAcceptedRhsCanonical
open AspisR1CurrentWide.Proof AspisR1FinishDotSourceABI
open AspisR1FinishRelationCurrent

def withSourceDotFinish {W : Type} (base : FinishOps W PushState) : FinishOps W PushState :=
  {base with finishDot:=finishFromPush,eq:=finishEq}

theorem successful_query_dot_canonical {W : Type}
    (base : FinishOps W PushState) (fm : Slice U8)
    (ws : Slice aspis_core.field.QM31) (out : FinishE)
    (hrun : verifier.finish_query_dot (withSourceDotFinish base) fm ws = .ok (.Ok out)) :
    CanonicalFinish out := by
  obtain ⟨initial,final,hnew,hchain,hfinish⟩ :=
    FinishCandidateDotTrace.finish_success_trace (withSourceDotFinish base) fm ws out hrun
  exact (finishFromPush_success_canonical final out hfinish).1

theorem successful_S2_finish_rhs_canonical {W : Type}
    (base : FinishOps W PushState) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
    (hv : p.variant=transport.Variant.S2)
    (hrun : verifier.finish_relation (withSourceDotFinish base) v p a obs = .ok (.Ok ())) :
    CanonicalFinish a.rhs := by
  have faithful : ∀ x y, (withSourceDotFinish base).eq x y=.ok true → x=y :=
    finish_eq_success_true
  obtain ⟨alpha0,claim1,alpha1,claim2,w,sliced,pair,actual,
    h0,hr0,h1,hr1,hw,hs,hpair,hpairEq,hdot,heq,hnext⟩ :=
    FinishCandidateEquations.s2_success_equations (withSourceDotFinish base)
      faithful v p a obs hv hrun
  have hc := successful_query_dot_canonical base v.final_message
    (alloc.vec.Vec.deref a.weights) actual hdot
  rw [heq] at hc
  exact hc

#print axioms successful_query_dot_canonical
#print axioms successful_S2_finish_rhs_canonical
end AspisR1FinishAcceptedRhsCanonical
