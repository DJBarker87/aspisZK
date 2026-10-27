import FJf_FactorArray
import FJf_Coordinates
import FJf_DigitValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PointCell
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)
open FJc_WeightQMBridge (SQ)
open FJf_FactorArray (canon value)

def point (p : Array SQ 10#usize) (d : Nat) (s : Fin 4) : OraclePortCheckpointAbiC5.K :=
  FJd_PointReference.factors
    (FJc_WeightArray.value p (9-2*FJf_PointIndices.tau d))
    (FJc_WeightArray.value p (8-2*FJf_PointIndices.tau d)) s

/-- VALUE and complete frame of one installed point-factor iteration. -/
theorem value_step (points : Points) (k : Usize) (p : Array SQ 10#usize)
    (hp : Array.index_usize points k=ok p) (hc : FJc_WeightArray.canonical p)
    (iter cursor : FIo_RangeNext.Range) (factors next : Factors) (hf : canon factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0.body points k iter factors=
      ok (.cont (cursor,next))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    canon next ∧ ∀ (j d : Nat) (s : Fin 4),
      value next j d s.val=if k.val=j ∧ iter.start.val=d then point p d s
        else value factors j d s.val := by
  obtain ⟨di,tau,ia,ib,p',a,b,row,back,updated,f0,f1,f2,f3,
    hn,ht,hia,hib,hp',ha,hb,href,hrow,hupdated,hnext⟩ :=
    FJf_PointBody.source points k iter cursor factors next run
  have ep := Result.ok.inj (hp.symm.trans hp')
  subst p'
  have va := FJc_WeightArray.read p ia a ha
  have vb := FJc_WeightArray.read p ib b hb
  have ca := FJc_WeightArray.canonical_read p ia a hc ha
  have cb := FJc_WeightArray.canonical_read p ib b hc hb
  have digit := FJf_DigitValue.value a b f0 f1 f2 f3 ca cb href
  have ti := FJf_PointIndices.tau_read di tau ht
  have ci := FJf_Coordinates.indices tau ti.2.1
  have vd : ∀ s : Fin 4,
      FJc_WeightArray.value (Array.make 4#usize [f0,f1,f2,f3]) s.val=point p di.val s := by
    intro s
    rw [digit.2 s,←va,←vb,hia,hib,ci.1,ci.2,ti.2.2]
    rfl
  obtain ⟨readRow,eb⟩ := FJf_ArrayOps.index_mut factors k row back hrow
  have cr : FJf_FactorArray.rowCanon row :=
    hf row (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ readRow))
  have cu := FJf_FactorArray.row_update_canon row updated di _ cr digit.1 hupdated
  have progress := FIo_RangeNext.some_next iter cursor di hn
  rw [eb] at hnext
  subst next
  refine ⟨progress.2.1,progress.2.2.1,progress.2.2.2,
    FJf_FactorArray.outer_set_canon factors k updated hf cu,?_⟩
  intro j d s
  rw [FJf_FactorArray.outer_set factors k row updated readRow j d s.val]
  by_cases hk : k.val=j
  · rw [if_pos hk,FJf_FactorArray.row_update row updated di _ hupdated d s.val]
    by_cases hd : iter.start.val=d
    · rw [progress.1,if_pos hd,if_pos ⟨hk,hd⟩,vd]
      rw [progress.1,hd]
    · rw [progress.1,if_neg hd,if_neg (by tauto)]
      rw [←FJf_FactorArray.row_read factors k row readRow d s.val,hk]
  · rw [if_neg hk,if_neg (by tauto)]
#print axioms value_step
end AspisR1.FJf_PointCell
end
