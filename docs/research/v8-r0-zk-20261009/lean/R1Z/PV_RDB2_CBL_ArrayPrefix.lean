import R1Z.PV_RDB2_CBL_ArrayKernel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayPrefix
set_option autoImplicit false

def copied {T : Type} [Inhabited T] {N : Usize} (out : Array T N) (v : Slice T) (k : Nat) : Prop :=
  ∀ j, j<k → j<N.val → out.val[j]! = v.val[j]!

theorem set_get {T : Type} [Inhabited T] {N : Usize} (out : Array T N) (i : Usize)
    (x : T) (j : Nat) (hi : i.val<N.val) :
    (out.set i x).val[j]! = if j=i.val then x else out.val[j]! := by
  simp only [Array.set_val_eq]
  by_cases h : j=i.val
  · subst j
    simp [List.getElem!_eq_getElem?_getD,
      List.getElem?_set_self (show i.val<out.val.length by simpa [out.property] using hi)]
  · simp [List.getElem!_eq_getElem?_getD,h]

theorem advance {T : Type} [Inhabited T] {N : Usize} (out : Array T N) (v : Slice T)
    (i : Usize) (hi : i.val<N.val) (hv : i.val<v.val.length) (h : copied out v i.val) :
    copied (out.set i v.val[i.val]) v (i.val+1) := by
  intro j hj hn
  rw [set_get _ _ _ _ hi]
  split
  · next e => subst j; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hv]
  · next e => exact h j (by omega) hn

theorem initial {T : Type} [Inhabited T] {N : Usize} (out : Array T N) (v : Slice T) :
    copied out v 0 := by intro j h; omega
#print axioms copied
#print axioms set_get
#print axioms advance
#print axioms initial
end R1Z.PV_CBL_ArrayPrefix
