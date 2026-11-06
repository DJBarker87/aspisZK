import NKI_RangeModel
import NJX_RangeInvocation
import RPv_FIx_ValueBitPrefix
import RPv_FIx_SelectedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_RangeCohort
open Aeneas Aeneas.Std
open FIv_NativeValue (decode K)
open NJX_RangeInvocation (Openings xs)
def model (o : Openings) : Fin 33 → K :=
 NKI_RangeModel.closed 2 (xs o 2) (NKI_RangeModel.closed 1 (xs o 1) (NKI_RangeModel.closed 0 (xs o 0) (fun _=>0)))
theorem read (o : Openings) (v : Fin 3) (i : Fin 10) :
 decode (xs o v i)=FIv_NativeArray.value (NJX_RangeInvocation.views o v) i.val :=
 (FIx_SelectedMeaning.read _ i.val (by have h:=i.isLt;scalar_tac)).symm

theorem source (o : Openings) : model o=FIx_ValueBitPrefix.model o (fun _=>0) := by
 funext j
 by_cases h10 : j.val<10
 · rw [model,NKI_RangeModel.closed,dif_neg (by omega),NKI_RangeModel.closed,dif_neg (by omega),NKI_RangeModel.closed,dif_pos (by omega),FIx_ValueBitPrefix.model,if_pos h10]
   simp only [NKI_RangeModel.value,read]
   change FIv_NativeArray.value o.z j.val*FIv_NativeArray.value o.z j.val-FIv_NativeArray.value o.z j.val=FIx_ValueBitModel.bit o.z j.val
   unfold FIx_ValueBitModel.bit
   ring
 · by_cases h20 : j.val<20
   · rw [model,NKI_RangeModel.closed,dif_neg (by omega),NKI_RangeModel.closed,dif_pos (by omega),FIx_ValueBitPrefix.model,if_neg h10,if_pos h20]
     simp only [NKI_RangeModel.value,read]
     change FIv_NativeArray.value o.succ_z (j.val-10)*FIv_NativeArray.value o.succ_z (j.val-10)-FIv_NativeArray.value o.succ_z (j.val-10)=FIx_ValueBitModel.bit o.succ_z (j.val-10)
     unfold FIx_ValueBitModel.bit
     ring
   · by_cases h30 : j.val<30
     · rw [model,NKI_RangeModel.closed,dif_pos (by omega),FIx_ValueBitPrefix.model,if_neg h10,if_neg h20,if_pos h30]
       simp only [NKI_RangeModel.value,read]
       change FIv_NativeArray.value o.xor12_z (j.val-20)*FIv_NativeArray.value o.xor12_z (j.val-20)-FIv_NativeArray.value o.xor12_z (j.val-20)=FIx_ValueBitModel.bit o.xor12_z (j.val-20)
       unfold FIx_ValueBitModel.bit
       ring
     · rw [model,NKI_RangeModel.closed,dif_neg (by omega),NKI_RangeModel.closed,dif_neg (by omega),NKI_RangeModel.closed,dif_neg (by omega),FIx_ValueBitPrefix.model,if_neg h10,if_neg h20,if_neg h30]
#print axioms read
#print axioms source
end AspisR1.NKI_RangeCohort
end
