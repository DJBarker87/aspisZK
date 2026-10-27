import FJm_LibraStages
import FJf_QMArray
import FJc_WeightConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraPowerValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (extra : Array NQ 2#usize) (side : Usize)
    (hc : ∀ q∈extra.val,FIo_QMValues.Canon q)
    (base high : Array NQ 4#usize) (q4 q16 : NQ)
    (run : FJm_LibraStages.powers extra side=ok (base,high,q4,q16)) :
    ∃ q : NQ,Array.index_usize extra side=ok q ∧ FIo_QMValues.Canon q ∧
      FJf_QMArray.canon base ∧ FJf_QMArray.canon high ∧
      (∀ s : Fin 4,FJf_QMArray.value base s.val=decodeQM (qm q)^s.val) ∧
      (∀ s : Fin 4,FJf_QMArray.value high s.val=decodeQM (qm q)^(4*s.val)) ∧
      FIo_QMValues.Canon q4 ∧ FIo_QMValues.Canon q16 ∧
      decodeQM (qm q4)=decodeQM (qm q)^4 ∧ decodeQM (qm q16)=decodeQM (qm q)^16 := by
  unfold FJm_LibraStages.powers at run
  obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q3,hq3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨ignored,hignored,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨read2,hread2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨four,hfour,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨eight,height,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨twelve,htwelve,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨sixteen,hsixteen,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have sameRead : read2=q2 := by
    have read : Array.index_usize (Array.make 4#usize
      [FIo_Native.aspis_core.field.QM31.ONE,q1,q2,q3]) 2#usize=ok q2 := rfl
    exact Result.ok.inj (hread2.symm.trans read)
  subst read2
  have cq : FIo_QMValues.Canon q := hc q (List.mem_of_getElem? (FJc_ReadSlot.slot extra side q hq))
  have cOne : FIo_QMValues.Canon FIo_Native.aspis_core.field.QM31.ONE := FJc_WeightConstants.one.1
  have vOne : decodeQM (qm FIo_Native.aspis_core.field.QM31.ONE)=1 := FJc_WeightConstants.one.2
  have v1 := FIo_QMMulValues.mul _ q q1 cOne cq hq1
  have v2 := FIo_QMMulValues.mul q1 q q2 v1.1 cq hq2
  have v3 := FIo_QMMulValues.mul q2 q q3 v2.1 cq hq3
  have v4 := FJm_QMSquare.value q2 four v2.1 hfour
  have v8 := FJm_QMSquare.value four eight v4.1 height
  have v12 := FIo_QMMulValues.mul eight four twelve v8.1 v4.1 htwelve
  have v16 := FJm_QMSquare.value eight sixteen v8.1 hsixteen
  have p1 : decodeQM (qm q1)=decodeQM (qm q) := by rw [v1.2,vOne,one_mul]
  have p2 : decodeQM (qm q2)=decodeQM (qm q)^2 := by rw [v2.2,p1];ring
  have p3 : decodeQM (qm q3)=decodeQM (qm q)^3 := by rw [v3.2,p2];ring
  have p4 : decodeQM (qm four)=decodeQM (qm q)^4 := by rw [v4.2,p2];ring
  have p8 : decodeQM (qm eight)=decodeQM (qm q)^8 := by rw [v8.2,p4];ring
  have p12 : decodeQM (qm twelve)=decodeQM (qm q)^12 := by rw [v12.2,p8,p4];ring
  have p16 : decodeQM (qm sixteen)=decodeQM (qm q)^16 := by rw [v16.2,p8];ring
  cases Result.ok.inj run
  refine ⟨q,hq,cq,?_,?_,?_,?_,v4.1,v16.1,p4,p16⟩
  · intro x hx
    change x∈[FIo_Native.aspis_core.field.QM31.ONE,q1,q2,q3] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  · intro x hx
    change x∈[FIo_Native.aspis_core.field.QM31.ONE,four,eight,twelve] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  · intro s
    fin_cases s <;> simpa only [FJf_QMArray.value,Array.make,List.getElem?_cons_zero,
      List.getElem?_cons_succ,pow_zero,pow_one] using (by first | exact vOne | exact p1 | exact p2 | exact p3)
  · intro s
    fin_cases s <;> simpa only [FJf_QMArray.value,Array.make,List.getElem?_cons_zero,
      List.getElem?_cons_succ,pow_zero,pow_one] using (by first | exact vOne | exact p4 | exact p8 | exact p12)
#print axioms value
end AspisR1.FJm_LibraPowerValues
end
