import Aeneas
import Mathlib.Data.List.Forall2
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisR1S9OrderedNativeReadConsistencyV1

/-- The existing actual ordered-read relation determines the read at every
Fin position. No desired input values are supplied: they are the SAME list
values, paired to a source Usize whose value is precisely that position. -/
theorem ordered_forall2_get {A : Type} (R : Usize → A → Prop)
    (js : List Usize) (ps : List A) (n : Nat)
    (hlen : ps.length=n) (hreads : List.Forall₂ R js ps)
    (horder : js.map (fun j => j.val)=List.range' 0 n) (i : Fin n) :
    ∃ j : Usize, j.val=i.val ∧ R j (ps.get (Fin.cast hlen.symm i)) := by
  have hp : i.val < ps.length := by rw [hlen];exact i.isLt
  have hj : i.val < js.length := by rw [hreads.length_eq];exact hp
  let j : Usize := js.get ⟨i.val,hj⟩
  have hr : R j (ps.get (Fin.cast hlen.symm i)) := hreads.get hj hp
  have hsome : js[i.val]?=some j := List.getElem?_eq_getElem hj
  have hm : (js.map (fun j => j.val))[i.val]?=some j.val := by
    rw [List.getElem?_map,hsome]
    rfl
  rw [horder] at hm
  have hrg : (List.range' 0 n)[i.val]?=some i.val := by
    simpa only [Nat.zero_add,Nat.one_mul] using
      (List.getElem?_range' (s:=0) (step:=1) i.isLt)
  exact ⟨j,Option.some.inj (hm.symm.trans hrg),hr⟩

#print axioms ordered_forall2_get
end AspisR1S9OrderedNativeReadConsistencyV1
