import FJe_RawConversionValue
import FJb_BuilderTotal
import FIw_ArrayValue
import ExtractedMaskHornerStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_Base
open Aeneas Aeneas.Std Result FIq_Native
abbrev QM := FIv_NativeArithmetic.NQ
abbrev Exact := FIv_NativeValue.K
abbrev Decode := FIv_NativeValue.decode
abbrev Canonical := FIv_NativeValue.Canon
abbrev P := AspisV8R17.RawReducer.P
abbrev State := Array QM 16#usize
def cell {α : Type} {N : Usize} (a : Array α N) (i : Fin N.val) : α :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
def CanonicalState (a : State) : Prop := ∀ i : Fin 16, Canonical (cell a i)
theorem cell_set {α : Type} {N : Usize} (a : Array α N) (i : Usize)
    (x : α) (j : Fin N.val) :
    cell (a.set i x) j = if j.val = i.val then x else cell a j := by
  unfold cell
  by_cases heq : j.val = i.val
  · simp [heq,Array.set_val_eq]
  · have hne : i.val ≠ j.val := Ne.symm heq
    simp [Array.set_val_eq,List.getElem_set_ne,hne,heq]

theorem set_canonical (a : State) (i : Usize) (x : QM)
    (ha : CanonicalState a) (hx : Canonical x) : CanonicalState (a.set i x) := by
  intro j
  rw [cell_set]
  split
  · exact hx
  · exact ha j

theorem set_overwrite {α : Type} {N : Usize} (a : Array α N) (i : Usize)
    (x y : α) : (a.set i x).set i y = a.set i y := by
  apply Subtype.ext
  simp only [Array.set_val_eq,List.set_set]

#print axioms cell_set
#print axioms set_canonical
#print axioms set_overwrite
end AspisR1.FJh_Base
end
