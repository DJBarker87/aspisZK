import S8Kani2MutableSource
import S8Kani2MutableStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace S8Kani2MutableExtraction
namespace batched_weights
abbrev FinishIter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut aspis_core.field.QM31)
abbrev FinishBack := FinishIter → FinishIter
abbrev FinishSlice := Slice aspis_core.field.QM31

def prefixWrite (f : Nat → aspis_core.field.QM31) (start n : Nat) : FinishSlice → FinishSlice
  | s => match n with
    | 0 => s
    | k + 1 => prefixWrite f start k (if start ≤ k then s.setAtNat k (f k) else s)

theorem prefixWrite_before (f : Nat → aspis_core.field.QM31) (start n : Nat)
    (h : n ≤ start) (s : FinishSlice) : prefixWrite f start n s = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [prefixWrite]
      have hn : ¬ start ≤ n := by omega
      simp only [hn, ite_false]
      exact ih (by omega)

def BackPrefix (f : Nat → aspis_core.field.QM31) (start processed : Nat)
    (back : FinishBack) : Prop :=
  ∀ e : FinishIter, (back e).iter.slice = prefixWrite f start processed e.iter.slice

theorem backPrefix_id (f : Nat → aspis_core.field.QM31) (start : Nat) :
    BackPrefix f start start (fun e => e) := by
  intro e
  exact prefixWrite_before f start start (Nat.le_refl _) e.iter.slice |>.symm

theorem backPrefix_step (f : Nat → aspis_core.field.QM31)
    (start processed : Nat) (back : FinishBack) (index : Std.Usize)
    (nextBack : FinishIter → Option (Std.Usize × aspis_core.field.QM31) → FinishIter)
    (hback : BackPrefix f start processed back)
    (hindex : index.val = processed)
    (hstart : start ≤ processed)
    (hwrite : ∀ e : FinishIter,
      (nextBack e (some (index, f index.val))).iter.slice =
        e.iter.slice.setAtNat index.val (f index.val)) :
    BackPrefix f start (processed + 1)
      (fun e => back (nextBack e (some (index, f index.val)))) := by
  intro e
  rw [hback, hwrite]
  simp only [prefixWrite, if_pos hstart, hindex]
#print axioms prefixWrite_before

#print axioms backPrefix_id

#print axioms backPrefix_step

end batched_weights
end S8Kani2MutableExtraction
