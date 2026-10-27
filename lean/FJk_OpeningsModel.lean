import FJk_SelectorModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_OpeningsModel
open FIv_NativeValue (K)
open FJa_PoseidonOrigins (Openings)
/-- Native decoded cells are exactly the existing model's selected openings. -/
theorem value (o : Openings) :
    FJh_Native07RawValue.openings o=FIw_PublicModel.openings o := by
  have hz : FIw_ArrayValue.decoded o.z=fun i : Fin 16=>FIv_NativeArray.value o.z i.val := by
    funext i
    exact (FJh_LowModels.cell o.z i.val i.isLt).symm
  have hs : FIw_ArrayValue.decoded o.succ_z=fun i : Fin 16=>FIv_NativeArray.value o.succ_z i.val := by
    funext i
    exact (FJh_LowModels.cell o.succ_z i.val i.isLt).symm
  have hx : FIw_ArrayValue.decoded o.xor12_z=fun i : Fin 16=>FIv_NativeArray.value o.xor12_z i.val := by
    funext i
    exact (FJh_LowModels.cell o.xor12_z i.val i.isLt).symm
  unfold FJh_Native07RawValue.openings FIw_PublicModel.openings
  rw [hz,hs,hx]
#print axioms value
end AspisR1.FJk_OpeningsModel
end
