import RPu_FJr_CircleInnerCell
import RPu_FJf_CircleIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_CircleInnerWrite
open Aeneas Aeneas.Std Result ControlFlow
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (Canon decode)
open FJf_PointBody (Factors)
open FJf_FactorArray (canon value)

theorem value (k : Usize) (hk : k.val < 2) (iter cursor : FIo_RangeNext.Range)
    (factors next : Factors) (hf : canon factors) (x x' : SQ) (cx : Canon x)
    (run : FIn_WeightsExtract.weights_new_loop1_loop0.body k iter factors x=
      ok (.cont (cursor,next,x'))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    Canon x' ∧ decode x'=FJd_LoopReference.double (FJd_LoopReference.double (decode x)) ∧
    canon next ∧ ∀ (j d : Nat) (s : Fin 4),value next j d s.val=
      if 3+k.val=j ∧ iter.start.val=d then
        FJr_CircleInnerCell.quad (decode x) (FJd_LoopReference.double (decode x)) s
      else value factors j d s.val := by
  obtain ⟨he,hs,more,cx',vx',di,row,updated,back,digit,hdi,hr,hu,hnext,cd,vd⟩ :=
    FJr_CircleInnerCell.value k iter cursor factors next x x' cx run
  obtain ⟨readRow,eb⟩ := FJf_ArrayOps.index_mut factors _ row back hr
  have cr := hf row (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ readRow))
  have cu := FJf_FactorArray.row_update_canon row updated di digit cr cd hu
  rw [eb] at hnext
  subst next
  refine ⟨he,hs,more,cx',vx',FJf_FactorArray.outer_set_canon factors _ updated hf cu,?_⟩
  intro j d s
  rw [FJf_FactorArray.outer_set factors _ row updated readRow j d s.val,FJf_CircleIndex.value k hk]
  by_cases hj : 3+k.val=j
  · rw [if_pos hj,FJf_FactorArray.row_update row updated di digit hu d s.val,hdi]
    by_cases hd : iter.start.val=d
    · rw [if_pos hd,if_pos ⟨hj,hd⟩,vd]
    · rw [if_neg hd,if_neg (by tauto)]
      rw [←FJf_FactorArray.row_read factors _ row readRow d s.val,FJf_CircleIndex.value k hk,hj]
  · rw [if_neg hj,if_neg (by tauto)]

#print axioms value
end AspisR1.FJr_CircleInnerWrite
end
