import EbyKPushCheckedScalarCanonical
import DotPushSuccessResidues
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1EbyKPushDotBackend
abbrev PushDot := AspisR1EbyKPushExplicitOpsV1.Dot
abbrev PushQ := AspisR1EbyKPushExplicitOpsV1.Q
abbrev PushState := AspisR1EbyKPushExplicitOpsV1.State
abbrev PushWide := AspisR1EbyKPushExplicitOpsV1.Wide
abbrev PushQm := AspisR1EbyKPushExplicitOpsV1.Qm
abbrev RawFn := PushQ → PushQ → Result (Array U64 4#usize)

def dotViaRaw (rawFn : RawFn) (self : PushDot) (a b : PushQ) : Result PushDot := do
  let out ← AspisR1DotPushLocal.canonical.Dot.push rawFn ⟨self.sums⟩ a b
  .ok ⟨out.sums⟩

def pushWithDotBackend (rawFn : RawFn) (self : PushState) (value : PushWide) (scalar : PushQm) :=
  AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ
    AspisR1EbyKCheckedQConcreteAll.concreteAll (dotViaRaw rawFn) self value scalar

private theorem bind_success {α β : Type} (r : Result α) (f : α → Result β) (y : β)
    (h : Bind.bind r f = .ok y) : ∃ x, r=.ok x ∧ f x=.ok y := by
  cases r with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h

theorem dotViaRaw_success (rawFn : RawFn) (self : PushDot) (a b : PushQ) (out : PushDot)
    (hrun : dotViaRaw rawFn self a b = .ok out) :
    ∃ raw : Array U64 4#usize,
      rawFn a b = .ok raw ∧
      out.sums=AspisR1DotPushLocal.Proof.updatedSums self.sums raw := by
  unfold dotViaRaw at hrun
  obtain ⟨d,hd,he⟩ := bind_success _ _ _ hrun
  obtain ⟨raw,hraw,hs⟩ := AspisR1DotPushLocal.Proof.push_success_raw_and_state
    rawFn ⟨self.sums⟩ a b d hd
  have hout : (⟨d.sums⟩ : PushDot)=out := Result.ok.inj he
  exact ⟨raw,hraw,by rw [←hout];exact hs⟩

abbrev scalarQ (s : PushQm) : PushQ := Array.make 4#usize [s.c0.a,s.c0.b,s.c1.a,s.c1.b]
abbrev valueLo (v : PushWide) : PushQ := AspisR1EbyKPushWideToQ.qFromCoords
  v.c0.c0.a v.c0.c0.b v.c0.c1.a v.c0.c1.b
abbrev valueHi (v : PushWide) : PushQ := AspisR1EbyKPushWideToQ.qFromCoords
  v.c1.c0.a v.c1.c0.b v.c1.c1.a v.c1.c1.b

theorem successful_push_exact_backend (rawFn : RawFn)
    (self : PushState) (value : PushWide) (scalar : PushQm) (out : PushState)
    (hrun : pushWithDotBackend rawFn self value scalar = .ok (.Ok (),out)) :
    ∃ lo hi : Array U64 4#usize,
      rawFn (valueLo value) (scalarQ scalar)=.ok lo ∧
      rawFn (valueHi value) (scalarQ scalar)=.ok hi ∧
      out.c0.sums=AspisR1DotPushLocal.Proof.updatedSums self.c0.sums lo ∧
      out.c1.sums=AspisR1DotPushLocal.Proof.updatedSums self.c1.sums hi ∧
      self.count < AspisR1EbyKPushExplicitOpsV1.maxTerms ∧
      out.count.val=self.count.val+1 ∧
      ∀ x ∈ (scalarQ scalar).val, x.val<2147483647 := by
  have hshape := AspisR1EbyKPushConcreteCheckedQV1.push_concrete_checked_q_success
    AspisR1EbyKCheckedQConcreteAll.concreteAll (dotViaRaw rawFn) self value scalar out hrun
  rcases hshape with ⟨d0,d1,i,hd0,hd1,hout,hcount,hinc⟩
  obtain ⟨lo,hlo,hloState⟩ := dotViaRaw_success rawFn self.c0 _ _ d0 hd0
  obtain ⟨hi,hhi,hhiState⟩ := dotViaRaw_success rawFn self.c1 _ _ d1 hd1
  have hcanonical := AspisR1EbyKPushCheckedScalarCanonical.successful_push_scalar_canonical
    (dotViaRaw rawFn) self value scalar out hrun
  refine ⟨lo,hi,hlo,hhi,?_,?_,hcount,hinc,hcanonical⟩
  · rw [hout];exact hloState
  · rw [hout];exact hhiState

#print axioms dotViaRaw_success
#print axioms successful_push_exact_backend
end AspisR1EbyKPushDotBackend
