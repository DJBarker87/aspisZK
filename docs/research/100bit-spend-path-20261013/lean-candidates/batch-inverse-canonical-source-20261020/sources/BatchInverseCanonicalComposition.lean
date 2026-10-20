import BatchBackwardEntrypointCanonical
import BatchInverseSourceComposition
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchBackward.Proof
open R17CurrentM31Semantics alloc.vec

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem runCandidate_success_canonical (flat out : Vec U32)
    (h : runCandidate flat = .ok out) : CanonicalVec out := by
  unfold runCandidate at h
  rcases bind_ok_inv h with ⟨pair,_,hback⟩
  rcases pair with ⟨pref,product⟩
  exact backward_success_canonical currentInv flat pref product out hback

theorem runCandidate_success_correct (flat out : Vec U32)
    (hnonzero : ∀ x ∈ flat.val, decode x ≠ 0)
    (h : runCandidate flat = .ok out) :
    CanonicalVec out ∧ out.val.map decode = (flat.val.map decode).map Inv.inv :=
  ⟨runCandidate_success_canonical flat out h,runCandidate_success_inverses flat out hnonzero h⟩

#print axioms runCandidate_success_canonical
#print axioms runCandidate_success_correct
end AspisR1BatchBackward.Proof
