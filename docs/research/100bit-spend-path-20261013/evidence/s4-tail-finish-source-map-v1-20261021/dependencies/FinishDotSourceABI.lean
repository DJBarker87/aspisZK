import EbyKPushDotBackend
import CurrentEbyFinishCanonical
import CurrentFinishArithmetic
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotSourceABI
open AspisR1CurrentWide.Proof
abbrev PushState := AspisR1EbyKPushDotBackend.PushState
abbrev FinishState := AspisR1EbyKFinish.EbyKDot

def toFinishState (s : PushState) : FinishState :=
  ⟨⟨s.c0.sums⟩,⟨s.c1.sums⟩,s.count⟩

def finishFromPush (s : PushState) : Result FinishE := do
  let out ← AspisR1EbyKFinish.EbyKDot.finish (toFinishState s)
  .ok (toFinishE (AspisR1EbyKFinish.Proof.toCurrentWide out))

def finishWords (v : FinishE) : List U32 :=
  [v.c0.c0.a,v.c0.c0.b,v.c0.c1.a,v.c0.c1.b,
   v.c1.c0.a,v.c1.c0.b,v.c1.c1.a,v.c1.c1.b]

theorem finishFromPush_total (s : PushState) :
    ∃ out : FinishE, finishFromPush s=.ok out ∧ CanonicalFinish out ∧
      finishWords out = (s.c0.sums.val++s.c1.sums.val).map AspisR1EbyKFinish.Proof.word := by
  obtain ⟨result,hr,hwords,hcanon⟩ := AspisR1EbyKFinish.Proof.eby_finish_total (toFinishState s)
  have hc := (AspisR1EbyKFinish.Proof.finish_output_current_canonical (toFinishState s) result hr).1
  refine ⟨toFinishE (AspisR1EbyKFinish.Proof.toCurrentWide result),?_,?_,?_⟩
  · simp only [finishFromPush,hr,bind_tc_ok]
  · change CanonicalWide (ofFinishE (toFinishE _))
    rw [of_to_finish]
    exact hc
  · change AspisR1EbyKFinish.Proof.finishLimbs result = _
    exact hwords

theorem finishFromPush_success_canonical (s : PushState) (out : FinishE)
    (hrun : finishFromPush s=.ok out) : CanonicalFinish out ∧
      finishWords out = (s.c0.sums.val++s.c1.sums.val).map AspisR1EbyKFinish.Proof.word := by
  obtain ⟨v,hv,hc,hw⟩ := finishFromPush_total s
  have he : v=out := Result.ok.inj (hv.symm.trans hrun)
  subst v
  exact ⟨hc,hw⟩

#print axioms finishFromPush_total
#print axioms finishFromPush_success_canonical
end AspisR1FinishDotSourceABI
