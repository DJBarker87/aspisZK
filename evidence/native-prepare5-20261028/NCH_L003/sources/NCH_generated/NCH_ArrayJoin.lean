import NCA_SemanticFrames
set_option autoImplicit false
namespace AspisR1.NCH_ArrayJoin
open Aeneas Aeneas.Std

/-- Recover the model update from a native window's byte observations and
its verified modifies frame, on fixed before/after full carriers. -/
theorem source (before after : Array U8 14759#usize) {n : Usize}
    (bytes : Array U8 n) (start : Nat) (room : start+n.val≤14759)
    (values : ∀ k, k<n.val → after.val[start+k]! = bytes.val[k]!)
    (frame : ∀ k, k<14759 → (k<start ∨ start+n.val≤k) →
      after.val[k]!==before.val[k]!) :
    after=before.setSlice! start bytes.val := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [after.property,List.length_setSlice!,before.property]
  · intro k ha hb
    have index : k<14759 := by simpa only [after.property,UScalar.ofNatCore_val_eq] using ha
    have spec := NCA_SemanticFrames.window before bytes start k room index
    have eq : after.val[k]!=(before.setSlice! start bytes.val).val[k]! := by
      rw [spec]
      by_cases inside : start≤k ∧ k<start+n.val
      · rw [if_pos inside]
        have observed := values (k-start) (by omega)
        simpa only [Nat.add_sub_of_le inside.1] using observed
      · rw [if_neg inside]
        apply frame k index
        omega
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem ha,
      List.getElem?_eq_getElem hb,Option.getD_some] using eq

#print axioms source
end AspisR1.NCH_ArrayJoin
