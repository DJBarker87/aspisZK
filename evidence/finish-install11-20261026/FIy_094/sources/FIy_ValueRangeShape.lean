import FIy_ValuePacked
import FIw_PublicModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ValueRangeShape
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIy_ValueTail (Openings)
open FIy_FrontierStep (Selectors)

def unweighted (o : Openings) : Fin (33#usize).val → K :=
  FIy_ValueTail.model o (FIx_ValueBitPrefix.model o (fun _=>0))

theorem selector (s : Selectors) : FIy_ValuePacked.selector s=
    ((0+FIw_PublicModel.selector s 1008)+FIw_PublicModel.selector s 1010)+FIw_PublicModel.selector s 1012 := by
  rfl

theorem value (o : Openings) (j : Fin (33#usize).val) :
    unweighted o j=if j.val=32 then FIv_NativeArray.value o.xor12_z 10
      else if j.val=31 then FIv_NativeArray.value o.succ_z 10
      else if j.val=30 then FIv_NativeArray.value o.z 10-FIy_ValueTail.reconstruct o
      else if j.val<10 then FIx_ValueBitModel.bit o.z j.val
      else if j.val<20 then FIx_ValueBitModel.bit o.succ_z (j.val-10)
      else FIx_ValueBitModel.bit o.xor12_z (j.val-20) := by
  have bound : j.val<33 := j.isLt
  simp only [unweighted,FIy_ValueTail.model,FIx_ValueBitPrefix.model]
  by_cases h32 : j.val=32
  · have eq : j=(⟨32,by decide⟩ : Fin (33#usize).val) := Fin.ext h32
    subst j
    simp only [Function.update_self,↓reduceIte]
  · have ne32 : j≠(⟨32,by decide⟩ : Fin (33#usize).val) := fun h=>h32 (congrArg Fin.val h)
    rw [Function.update_of_ne ne32,if_neg h32]
    by_cases h31 : j.val=31
    · have eq : j=(⟨31,by decide⟩ : Fin (33#usize).val) := Fin.ext h31
      subst j
      simp only [Function.update_self,↓reduceIte]
    · have ne31 : j≠(⟨31,by decide⟩ : Fin (33#usize).val) := fun h=>h31 (congrArg Fin.val h)
      rw [Function.update_of_ne ne31,if_neg h31]
      by_cases h30 : j.val=30
      · have eq : j=(⟨30,by decide⟩ : Fin (33#usize).val) := Fin.ext h30
        subst j
        simp only [Function.update_self,↓reduceIte]
      · have ne30 : j≠(⟨30,by decide⟩ : Fin (33#usize).val) := fun h=>h30 (congrArg Fin.val h)
        rw [Function.update_of_ne ne30,if_neg h30,if_pos (show j.val<30 by omega)]
#print axioms selector
#print axioms value
end AspisR1.FIy_ValueRangeShape
end
