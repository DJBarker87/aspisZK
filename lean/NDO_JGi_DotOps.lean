import JGi_PushTotality
import NDO_JGg_PreparationOpening
set_option autoImplicit false
namespace AspisR1.JGi_DotOps
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim
abbrev ops := AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw
abbrev State := AspisR1S5ClaimDotConcreteAdapter.PushState
abbrev E := Concrete.E
abbrev Q := aspis_core.field.QM31
def CanonQ (q : Q) : Prop := AspisR1CurrentWide.Proof.CanonicalQM (Concrete.toQM q)

theorem pushCanonical (x : E) (h : Concrete.Canonical x) :
    AspisR1EbyKPowerValueCanonicalToPush.pushCanonical (AspisR1S5ClaimDotConcreteAdapter.toPushWide x) := by
  exact h
#print axioms pushCanonical

theorem scalarCanonical (q : Q) (h : CanonQ q) :
    ∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ (AspisR1S5ClaimDotConcreteAdapter.toPushQm q)).val,
      x.val < 2147483647 := by
  intro x hx
  change (q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647) ∧
    (q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647) at h
  simp only [AspisR1EbyKPushDotBackend.scalarQ,AspisR1S5ClaimDotConcreteAdapter.toPushQm,
    Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl
  · exact h.1.1
  · exact h.1.2
  · exact h.2.1
  · exact h.2.2
#print axioms scalarCanonical

theorem push (s : State) (x : E) (q : Q) (hx : Concrete.Canonical x)
    (hq : CanonQ q) (count : s.count.val<29) :
    ∃ out,ops.pushDot s x q=ok (.Ok (),out) ∧ out.count.val=s.count.val+1 := by
  obtain ⟨out,call⟩ := AspisR1S5EbyKPushTotalityV1.push_success_of_valid_scalar
    s (AspisR1S5ClaimDotConcreteAdapter.toPushWide x) (AspisR1S5ClaimDotConcreteAdapter.toPushQm q)
    (pushCanonical x hx) (by simp only [AspisR1EbyKPushExplicitOpsV1.maxTerms];scalar_tac) (scalarCanonical q hq)
  have step := AspisR1EbyKPushDotBackend.successful_push_exact_backend
    AspisR1EbyKPushDecodedProductUpdate.QRaw s _ _ out call
  obtain ⟨lo,hi,hlo,hhi,h0,h1,hcount,hinc,hscalar⟩ := step
  exact ⟨out,call,hinc⟩
#print axioms push

theorem finish (s : State) : ∃ out,ops.finishDot s=ok out ∧ Concrete.Canonical out := by
  obtain ⟨out,call,canonical,words⟩ := AspisR1FinishDotSourceABI.finishFromPush_total s
  refine ⟨ClaimParser.fromFinish out,?_,ClaimParser.canonical_from_finish out canonical⟩
  change (do let out ← AspisR1FinishDotSourceABI.finishFromPush s; ok (ClaimParser.fromFinish out))=_
  rw [call,bind_tc_ok]
#print axioms finish

theorem initial : ops.newDot=ok EbyKNewToPushStateABI.pushZero :=
  AspisR1FinishDotConcreteOps.sourceNewDot_zero
#print axioms initial
end AspisR1.JGi_DotOps
