import KSC2_MutFold
open Aeneas Aeneas.Std Result
namespace KSC2
-- A proposed guard repair, kept private and NOT offered as a certified
-- replacement for all borrow continuations or an adoption decision.
def guardedBack {T : Type} (s : core.slice.iter.IterMut T) :
    Result (Option T × core.slice.iter.IterMut T ×
      (core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T)) :=
  if s.i < s.slice.val.length then
    KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back s
  else ok (none,s,fun updated _ => updated)

theorem front_reaches_exhausted :
    (do let (v,s,_) ← core.slice.iter.IteratorIterMut.next (⟨singleton,0⟩ : core.slice.iter.IterMut Nat)
        ok (v,s)) = ok (some 7,exhausted) := rfl

theorem guarded_back_exhausted {T : Type} (s : core.slice.iter.IterMut T)
    (h : ¬ s.i < s.slice.val.length) :
    guardedBack s = ok (none,s,fun updated _ => updated) := by
  simp only [guardedBack,h,↓reduceIte]

theorem guarded_singleton :
    (do let (v,_,_) ← guardedBack exhausted; ok v : Result (Option Nat)) = ok none := by
  rw [guarded_back_exhausted exhausted (by decide)]
  rfl

theorem active_back_writeback (v : Nat) :
    (do let (item,s,restore) ← guardedBack (⟨two,0⟩ : core.slice.iter.IterMut Nat)
        ok (item,(restore s (some v)).slice.val) : Result (Option Nat × List Nat)) =
      ok (some 2,[1,v]) := by
  simp only [guardedBack]
  change (do let (item,s,restore) ←
    KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back
      (⟨two,0⟩ : core.slice.iter.IterMut Nat)
    ok (item,(restore s (some v)).slice.val)) = _
  rfl
#print axioms front_reaches_exhausted
#print axioms guarded_back_exhausted
#print axioms guarded_singleton
#print axioms active_back_writeback
end KSC2
