import RPv_FJa_ExpansionMeaning
import RPv_FJa_WeightAppend
import RPv_FJa_WeightPeriod
import RPv_FJa_BoxedMass
import RPv_FIw_PublicModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_BoxedLiteral
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
/-- Literal ten-coordinate point tensor of the SAME original boxed arrays.
No point/selector association is assumed. -/
theorem value (point : Array NQ 10#usize)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (hp : FIw_ArrayValue.canonical point)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s) :
    FIw_PublicModel.selector s=fun row=>FJa_TensorMeaning.weight (point.val.map decode) row.val := by
  obtain ⟨hi,lo,hhi,hhigh,hlo,hlow⟩ := FIz_BoxedOrigins.value point s run
  have hv := FJa_SlicesValue.high point hi hhi
  have lv := FJa_SlicesValue.low point lo hlo
  have sizeHi : (64#usize).val=2^hi.val.length := by rw [hv.2];decide
  have sizeLo : (16#usize).val=2^lo.val.length := by rw [lv.2];decide
  funext row
  have h := FJa_ExpansionMeaning.value 64#usize hi s.high (FJa_SliceBounds.high point hi hp hhi)
    sizeHi hhigh ⟨row.val/16,by have b:=row.isLt;change row.val/16<64;omega⟩
  have l := FJa_ExpansionMeaning.value 16#usize lo s.low (FJa_SliceBounds.low point lo hp hlo)
    sizeLo hlow ⟨row.val%16,by change row.val%16<16;omega⟩
  unfold FIw_PublicModel.selector
  rw [h,l]
  have concat : hi.val.map decode++lo.val.map decode=point.val.map decode := by
    rw [←List.map_append,hv.1,lv.1,List.take_append_drop]
  have lenLo : (lo.val.map decode).length=4 := by rw [List.length_map,lv.2]
  have split := FJa_WeightAppend.value (hi.val.map decode) (lo.val.map decode) row.val
  rw [concat,lenLo] at split
  have periodic := FJa_WeightPeriod.mod (lo.val.map decode) row.val
  rw [lenLo] at periodic
  change FJa_TensorMeaning.weight (lo.val.map decode) (row.val%16)=_ at periodic
  rw [periodic]
  exact split.symm
#print axioms value
end AspisR1.FJa_BoxedLiteral
end
