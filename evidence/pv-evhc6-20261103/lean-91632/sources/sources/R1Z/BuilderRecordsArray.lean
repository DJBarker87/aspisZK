import R1Z.BuilderRecordCanonical
import R0Z.WriterRefinePathBlock

/-! Small array facts for symbolic record-loop invariants. -/
set_option autoImplicit false
namespace R1Z.BuilderRecordsArray
open Aeneas Aeneas.Std Result R0Z.WriterRefine

def tabulate {α : Type} (n : Usize) (f : Nat → α) : Array α n :=
  ⟨List.ofFn (fun i : Fin n.val => f i.val), by simp⟩

theorem tabulate_get {α : Type} [Inhabited α] (n : Usize) (f : Nat → α)
    (i : Nat) (hi : i < n.val) : (tabulate n f).val[i]! = f i := by
  simp [tabulate, hi]

theorem update_gen {α : Type} {n : Usize} (v : Array α n) (i : Usize) (x : α)
    (hi : i.val < n.val) : Array.update v i x = ok (v.set i x) := by
  unfold Array.update
  rw [Array.getElem?_Usize_eq, List.getElem?_eq_getElem (by simpa [v.property] using hi)]
  rfl

theorem set_get {α : Type} [Inhabited α] {n : Usize}
    (v : Array α n) (i : Usize) (x : α) (j : Nat) (hi : i.val < n.val) :
    (v.set i x).val[j]! = if j = i.val then x else v.val[j]! := by
  simp only [Array.set_val_eq]
  by_cases h : j = i.val
  · subst j
    simp [List.getElem!_eq_getElem?_getD,
      List.getElem?_set_self (show i.val < v.val.length by simpa [v.property] using hi)]
  · simp [List.getElem!_eq_getElem?_getD, h]

def Prefix {α : Type} [Inhabited α] {n : Usize}
    (v target : Array α n) (k : Nat) : Prop :=
  ∀ j, j < k → j < n.val → v.val[j]! = target.val[j]!

theorem prefix_step {α : Type} [Inhabited α] {n : Usize}
    (v target : Array α n) (i : Usize) (hi : i.val < n.val)
    (h : Prefix v target i.val) :
    Prefix (v.set i target.val[i.val]!) target (i.val + 1) := by
  intro j hj hn
  rw [set_get _ _ _ _ hi]
  split
  · next e => exact congrArg (fun k => target.val[k]!) e.symm
  · next e => exact h j (by omega) hn

theorem prefix_done {α : Type} [Inhabited α] {n : Usize}
    (v target : Array α n) (h : Prefix v target n.val) : v = target := by
  apply BuilderRecordCanonical.array_ext
  intro j hj
  exact h j hj hj

theorem next_val (i : Usize) (hi : i.val < 24) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  rw [uadd _ _ (by simp; omega)]; rfl

#print axioms tabulate_get
#print axioms update_gen
#print axioms set_get
#print axioms prefix_step
#print axioms prefix_done
#print axioms next_val
end R1Z.BuilderRecordsArray
