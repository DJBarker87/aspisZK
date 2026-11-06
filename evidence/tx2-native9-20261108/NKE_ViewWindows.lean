import NJR_ViewFinish
set_option autoImplicit false
noncomputable section
namespace NKE_ViewWindows
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- A native fixed window at its actual absolute offset in the SAME proof. -/
def Window (proof output : Slice U8) (group : Fin 4) : Prop :=
 ∀ i,i<512 → output.val[512*group.val+i]?=proof.val[8007+512*group.val+i]?

theorem final_cells (proof output : Slice U8) (windows : ∀ group,Window proof output group)
 (i : Nat) (inside : i<2048) : output.val[i]?=proof.val[8007+i]? := by
 have groupBound : i/512<4 := by omega
 have laneBound : i%512<512 := Nat.mod_lt _ (by omega)
 have index : 512*(i/512)+i%512=i := by omega
 have cell := windows ⟨i/512,groupBound⟩ (i%512) laneBound
 simpa only [index,Subtype.val,Fin.val_mk,Nat.add_assoc] using cell

/-- All selected bytes plus the untouched length/frame identify the source
slice; no pointer-to-payload implication is used. -/
theorem slice_cells (proof output : Slice U8) (offset width : Nat)
 (range : offset+width≤proof.val.length) (size : output.val.length=width)
 (cells : ∀ i,i<width → output.val[i]?=proof.val[offset+i]?) :
 output.val=(proof.val.drop offset).take width := by
 have expectedSize : ((proof.val.drop offset).take width).length=width := by
  simp only [List.length_take,List.length_drop]
  omega
 apply List.ext_getElem?
 intro i
 by_cases inside : i<width
 · rw [cells i inside]
   simp only [List.getElem?_take,inside,if_true,List.getElem?_drop]
   congr 1
   omega
 · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
#print axioms final_cells
#print axioms slice_cells
end NKE_ViewWindows
