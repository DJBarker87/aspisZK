import FJe_PackedRawCallbacks
import FJb_TailCell
import RawPoseidonExternalRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedRawRowValue
open Aeneas Aeneas.Std Result
open FJb_RawRowCallbacks (Input)
open FJb_TailCell (cell)
def words (input : Input) (r j : Fin 4) : Nat := (cell (cell input r) j).val
/-- Raw matrix VALUE of the SAME packed callback. The old scalar arithmetic
proofs are imported; none is reevaluated or reproved. -/
theorem value (input : Input) (row limb : Usize) (hr : row.val<4) (hl : limb.val<4)
    (out : U64) (run : FJe_PackedRawCallbacks.call (input,row) limb=ok (out,(input,row))) :
    out.val=RawPoseidonExternalRows.rawRowNat
      (fun r=>words input r ⟨limb.val,hl⟩) ⟨row.val,hr⟩ := by
  have oldRun : FJb_RawRowCallbacks.reference (input,row) limb=ok (out,(input,row)) :=
    ((FJe_PackedRawCallbacks.same input row limb).trans
      (FJb_RawRowCallbacks.same input row limb)).symm.trans run
  obtain ⟨z0,z1,z2,z3,r0,v0,r1,v1,r2,v2,r3,v3⟩ :=
    RawPoseidonExternalAllRows.call_mut_all_lanes_of_array_bounds input limb hl
  have hc : row.val=0 ∨ row.val=1 ∨ row.val=2 ∨ row.val=3 := by omega
  rcases hc with h | h | h | h
  · have e : row=0#usize := UScalar.eq_of_val_eq h
    subst row
    have eo : out=z0 := congrArg Prod.fst (Result.ok.inj (oldRun.symm.trans r0))
    rw [eo]
    simpa only [RawPoseidonExternalRows.rawRowNat,RawPoseidonExternalRowReads.rawRowNat,
      words,cell,RawPoseidonExternalRowReads.limbValue,RawPoseidonExternalRowReads.rowValue] using v0
  · have e : row=1#usize := UScalar.eq_of_val_eq h
    subst row
    have eo : out=z1 := congrArg Prod.fst (Result.ok.inj (oldRun.symm.trans r1))
    rw [eo]
    simpa only [RawPoseidonExternalRows.rawRowNat,words,cell,
      RawPoseidonExternalRowReads.limbValue,RawPoseidonExternalRowReads.rowValue] using v1
  · have e : row=2#usize := UScalar.eq_of_val_eq h
    subst row
    have eo : out=z2 := congrArg Prod.fst (Result.ok.inj (oldRun.symm.trans r2))
    rw [eo]
    simpa only [RawPoseidonExternalRows.rawRowNat,words,cell,
      RawPoseidonExternalRowReads.limbValue,RawPoseidonExternalRowReads.rowValue] using v2
  · have e : row=3#usize := UScalar.eq_of_val_eq h
    subst row
    have eo : out=z3 := congrArg Prod.fst (Result.ok.inj (oldRun.symm.trans r3))
    rw [eo]
    simpa only [RawPoseidonExternalRows.rawRowNat,words,cell,
      RawPoseidonExternalRowReads.limbValue,RawPoseidonExternalRowReads.rowValue] using v3
#print axioms value
end AspisR1.FJe_PackedRawRowValue
end
