import RPu_FJr_CircleInnerLoop
import RPu_FJf_CircleOuterBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_CircleOuterCell
open Aeneas Aeneas.Std Result ControlFlow
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (Canon decode)
open FJf_PointBody (Factors)
open FJf_CircleOuterBody (Z)
open FJf_FactorArray (canon value)
abbrev FK := OraclePortCheckpointAbiC5.K

def digit (x y : FK) (d : Nat) (s : Fin 4) : FK :=
  if d=0 then FJr_CircleInnerCell.quad y x s
  else FJr_CircleInnerCell.quad
    (FJr_CircleInnerLoop.advance (FJd_LoopReference.double x) (d-1))
    (FJd_LoopReference.double (FJr_CircleInnerLoop.advance (FJd_LoopReference.double x) (d-1))) s

def CanonZ (z : Z) : Prop := ∀ p∈z.val,Canon p.x ∧ Canon p.y

theorem value (z : Z) (cz : CanonZ z) (iter cursor : FIo_RangeNext.Range)
    (factors next : Factors) (hf : canon factors) (he : iter.end.val=2)
    (run : FIn_WeightsExtract.weights_new_loop1.body z iter factors=ok (.cont (cursor,next))) :
    ∃ (k : Usize) (p : FIn_WeightsExtract.circle.SecureCirclePoint),
      k=iter.start ∧ cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
      Array.index_usize z k=ok p ∧ canon next ∧ ∀ j d s,
        value next j d s.val=if 3+k.val=j ∧ d<5 then digit (decode p.x) (decode p.y) d s
          else value factors j d s.val := by
  unfold FIn_WeightsExtract.weights_new_loop1.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none=>cases run
  | some k=>
    obtain ⟨p,hp,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨idx,hidx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨row,back⟩,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨updated,hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨x,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨last,hlast,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have ei := Result.ok.inj hidx
    subst idx
    have pr := FIo_RangeNext.some_next iter cursor k hn
    have hk : k.val < 2 := by rw [pr.1];omega
    have cp := cz p (List.mem_of_getElem? (FJc_ReadSlot.slot z k p hp))
    have vq := FJc_WeightValues.mul p.x p.y q cp.1 cp.2 hq
    have vx := FJr_DoubleValue.value p.x x cp.1 hx
    let dig := Array.make 4#usize [FIn_WeightsExtract.field.QM31.ONE,p.y,p.x,q]
    have cd : FJc_WeightArray.canonical dig := by
      intro v hv
      change v∈[FIn_WeightsExtract.field.QM31.ONE,p.y,p.x,q] at hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl|rfl|rfl
      · exact FJc_WeightConstants.one.1
      · exact cp.2
      · exact cp.1
      · exact vq.1
    have vd : ∀ s : Fin 4,FJc_WeightArray.value dig s.val=FJr_CircleInnerCell.quad (decode p.y) (decode p.x) s := by
      intro s
      fin_cases s
      · change decode FIn_WeightsExtract.field.QM31.ONE=1
        exact FJc_WeightConstants.one.2
      · rfl
      · rfl
      · change decode q=decode p.y*decode p.x
        rw [vq.2,mul_comm]
    obtain ⟨readRow,eb⟩ := FJf_ArrayOps.index_mut factors _ row back hr
    have cr := hf row (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ readRow))
    have cu := FJf_FactorArray.row_update_canon row updated 0#usize dig cr cd hu
    have cb : canon (back updated) := by
      rw [eb]
      exact FJf_FactorArray.outer_set_canon factors _ updated hf cu
    have inner := FJr_CircleInnerLoop.value k hk (back updated) next cb x vx.1 hlast
    refine ⟨k,p,pr.1,pr.2.1,pr.2.2.1,pr.2.2.2,hp,inner.1,?_⟩
    intro j d s
    rw [inner.2 j d s]
    unfold FJr_CircleInnerLoop.model
    rw [vx.2]
    by_cases hj : 3+k.val=j
    · by_cases hd : d=0
      · subst d
        simp only [hj,true_and,show ¬(1:Nat)≤0 from by omega,false_and,if_false]
        rw [eb,FJf_FactorArray.outer_set factors _ row updated readRow j 0 s.val,FJf_CircleIndex.value k hk,if_pos hj,
          FJf_FactorArray.row_update row updated 0#usize dig hu 0 s.val,if_pos (by rfl),vd]
        simp only [digit,ite_true,show (0:Nat)<5 from by omega,and_true,if_true]
      · by_cases hd5 : d<5
        · simp only [hj,hd5,true_and,if_true,and_true,show 1≤d from by omega,digit,if_neg hd]
        · simp only [hj,hd5,true_and,and_false,if_false]
          rw [eb,FJf_FactorArray.outer_set factors _ row updated readRow j d s.val,FJf_CircleIndex.value k hk,if_pos hj,
            FJf_FactorArray.row_update row updated 0#usize dig hu d s.val,if_neg (by simpa using Ne.symm hd)]
          rw [←FJf_FactorArray.row_read factors _ row readRow d s.val,FJf_CircleIndex.value k hk,hj]
    · simp only [hj,false_and,if_false]
      rw [eb,FJf_FactorArray.outer_set factors _ row updated readRow j d s.val,FJf_CircleIndex.value k hk,if_neg hj]

#print axioms value
end AspisR1.FJr_CircleOuterCell
end
