import RPu_FJc_InactiveCoefficientsModel
import RPu_FJr_InactiveRegistry
import RPu_FJr_InactiveRowIndex
import RPu_FJc_MaskTable
import R1D18OpeningWeights
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_InactiveRaw
abbrev FE := OraclePortCheckpointAbiC5.E

def raw : Fin 1024 → FE := AspisR0.Opening.coeffWeight rowEquiv
  (AspisR0.Opening.indicator R0P.copyInactiveRows)

theorem value (i : Fin 64) (s t : Fin 4) :
    raw (childIndex (childIndex i s) t)=
      if (FJc_SubsetModel.mask (FJc_InactiveCoefficientsModel.group i.val) &&& 2^(4*s.val+t.val))≠0 then 1 else 0 := by
  unfold raw
  rw [coeffWeight_indicator_eq_rowIndicator]
  have mr := FJr_InactiveRegistry.member (row (childIndex (childIndex i s) t))
  have rowValue : (row (childIndex (childIndex i s) t)).val=FJc_S2Rows.row i.val (4*s.val+t.val) :=
    FJr_InactiveRowIndex.value i s t
  rw [rowValue] at mr
  change FJc_S2Rows.inactive i.val (4*s.val+t.val) ↔ _ at mr
  simp only [←mr,←FJc_MaskTable.value i.val (4*s.val+t.val) i.isLt (by have:=s.isLt;have:=t.isLt;omega)]
  rfl

#print axioms value
end AspisR1.FJr_InactiveRaw
end
