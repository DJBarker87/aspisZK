import SAG_DotClosed
import JGi_PushTotality
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotOps
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide.Proof AspisR1FinishDotSourceABI AspisR1FinishRelationCurrent
abbrev State := AspisR1EbyKPushDotBackend.PushState
abbrev E := FinishE
abbrev Q := FinishQM
abbrev ops := AspisR1FinishDotConcreteOps.withConcreteDot
  (finishConcreteField SAG_DotClosed.seed) AspisR1EbyKPushDecodedProductUpdate.QRaw

theorem scalar (q : Q) (h : CanonicalQM q) :
    ∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ (AspisR1FinishDotConcreteOps.toPushQM q)).val,
      x.val<2147483647 := by
  intro x hx
  change (q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647) ∧
    (q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647) at h
  simp only [AspisR1EbyKPushDotBackend.scalarQ,AspisR1FinishDotConcreteOps.toPushQM,
    Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl
  · exact h.1.1
  · exact h.1.2
  · exact h.2.1
  · exact h.2.2
#print axioms scalar

theorem push (s : State) (x : E) (q : Q) (hx : CanonicalFinish x)
    (hq : CanonicalQM q) (count : s.count.val<64) :
    ∃ out,ops.pushDot s x q=ok (.Ok (),out) ∧ out.count.val=s.count.val+1 := by
  obtain ⟨out,call⟩ := AspisR1S5EbyKPushTotalityV1.push_success_of_valid_scalar
    s (AspisR1FinishDotConcreteOps.toPushWide x) (AspisR1FinishDotConcreteOps.toPushQM q)
    hx (by simp only [AspisR1EbyKPushExplicitOpsV1.maxTerms];scalar_tac) (scalar q hq)
  obtain ⟨lo,hi,hlo,hhi,h0,h1,hcount,hinc,hscalar⟩ :=
    AspisR1EbyKPushDotBackend.successful_push_exact_backend
      AspisR1EbyKPushDecodedProductUpdate.QRaw s _ _ out call
  exact ⟨out,call,hinc⟩
#print axioms push

theorem finish (s : State) : ∃ out,ops.finishDot s=ok out ∧ CanonicalFinish out := by
  obtain ⟨out,call,canonical,words⟩ := finishFromPush_total s
  exact ⟨out,call,canonical⟩
#print axioms finish

theorem initial : ops.newDot=ok EbyKNewToPushStateABI.pushZero :=
  AspisR1FinishDotConcreteOps.sourceNewDot_zero
#print axioms initial
end AspisR1.JGv_DotOps
end
