import R1Z.PV_RunJoin_CopyCertificate20
import R1Z.PV_RunJoin_BankCells4519
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell4520
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell4519.certificate.pre) i +
    (liftA PV_RunJoin_BankCell4519.certificate.absorption) i else (liftA PV_RunJoin_BankCell4519.certificate.pre) i) = s_45_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 1 = s_45_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell4519.certificate.pre) (liftA PV_RunJoin_BankCell4519.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_45_1,round_45_2]
  exact round_45_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 2 = s_45_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_45_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_45_3 = s_45_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_45_3).trans round_45_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_45_4 = s_45_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_45_4).trans round_45_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 3 = s_45_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_45_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_45_5 = s_45_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_45_5).trans round_45_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_45_6 = s_45_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_45_6).trans round_45_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 4 = s_45_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_45_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_45_7 = s_45_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_45_7).trans round_45_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_45_8 = s_45_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_45_8).trans round_45_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 5 = s_45_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_45_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_45_9 = s_45_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_45_9).trans round_45_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_45_10 = s_45_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_45_10).trans round_45_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 6 = s_45_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_45_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_45_11 = s_45_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_45_11).trans round_45_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_45_12 = s_45_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_45_12).trans round_45_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 7 = s_45_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_45_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_45_13 = s_45_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_45_13).trans round_45_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_45_14 = s_45_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_45_14).trans round_45_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 8 = s_45_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_45_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_45_15 = s_45_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_45_15).trans round_45_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_45_16 = s_45_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_45_16).trans round_45_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 9 = s_45_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_45_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_45_17 = s_45_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_45_17).trans round_45_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_45_18 = s_45_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_45_18).trans round_45_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 10 = s_45_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_45_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_45_19 = s_45_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_45_19).trans round_45_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_45_20 = s_45_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_45_20).trans round_45_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) 11 = s_45_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_45_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_45_21 = s_45_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_45_21).trans round_45_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_45_22 = s_45_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_45_22).trans round_45_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell4519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell4519.canon3
  · exact PV_RunJoin_ValidatorCell4519.canon5
  · exact PV_RunJoin_ValidatorCell4519.canon7
  · exact PV_RunJoin_ValidatorCell4519.canon9
  · exact PV_RunJoin_ValidatorCell4519.canon11
  · exact PV_RunJoin_ValidatorCell4519.canon13
  · exact PV_RunJoin_ValidatorCell4519.canon15
  · exact PV_RunJoin_ValidatorCell4519.canon17
  · exact PV_RunJoin_ValidatorCell4519.canon19
  · exact PV_RunJoin_ValidatorCell4519.canon21
  · exact PV_RunJoin_ValidatorCell4519.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4519.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell4519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell4519.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell4519.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell4519.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell4519.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell4519.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell4519.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell4519.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell4519.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell4519.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell4519.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell4519.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell4519.certificate.pre PV_RunJoin_BankCell4519.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell4519.certificate.pre PV_RunJoin_BankCell4519.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell4519.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell4520

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell4620
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell4619.certificate.pre) i +
    (liftA PV_RunJoin_BankCell4619.certificate.absorption) i else (liftA PV_RunJoin_BankCell4619.certificate.pre) i) = s_46_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 1 = s_46_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell4619.certificate.pre) (liftA PV_RunJoin_BankCell4619.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_46_1,round_46_2]
  exact round_46_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 2 = s_46_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_46_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_46_3 = s_46_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_46_3).trans round_46_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_46_4 = s_46_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_46_4).trans round_46_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 3 = s_46_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_46_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_46_5 = s_46_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_46_5).trans round_46_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_46_6 = s_46_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_46_6).trans round_46_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 4 = s_46_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_46_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_46_7 = s_46_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_46_7).trans round_46_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_46_8 = s_46_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_46_8).trans round_46_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 5 = s_46_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_46_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_46_9 = s_46_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_46_9).trans round_46_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_46_10 = s_46_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_46_10).trans round_46_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 6 = s_46_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_46_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_46_11 = s_46_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_46_11).trans round_46_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_46_12 = s_46_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_46_12).trans round_46_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 7 = s_46_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_46_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_46_13 = s_46_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_46_13).trans round_46_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_46_14 = s_46_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_46_14).trans round_46_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 8 = s_46_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_46_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_46_15 = s_46_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_46_15).trans round_46_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_46_16 = s_46_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_46_16).trans round_46_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 9 = s_46_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_46_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_46_17 = s_46_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_46_17).trans round_46_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_46_18 = s_46_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_46_18).trans round_46_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 10 = s_46_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_46_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_46_19 = s_46_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_46_19).trans round_46_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_46_20 = s_46_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_46_20).trans round_46_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) 11 = s_46_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_46_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_46_21 = s_46_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_46_21).trans round_46_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_46_22 = s_46_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_46_22).trans round_46_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell4619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell4619.canon3
  · exact PV_RunJoin_ValidatorCell4619.canon5
  · exact PV_RunJoin_ValidatorCell4619.canon7
  · exact PV_RunJoin_ValidatorCell4619.canon9
  · exact PV_RunJoin_ValidatorCell4619.canon11
  · exact PV_RunJoin_ValidatorCell4619.canon13
  · exact PV_RunJoin_ValidatorCell4619.canon15
  · exact PV_RunJoin_ValidatorCell4619.canon17
  · exact PV_RunJoin_ValidatorCell4619.canon19
  · exact PV_RunJoin_ValidatorCell4619.canon21
  · exact PV_RunJoin_ValidatorCell4619.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4619.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell4619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell4619.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell4619.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell4619.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell4619.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell4619.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell4619.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell4619.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell4619.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell4619.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell4619.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell4619.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell4619.certificate.pre PV_RunJoin_BankCell4619.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell4619.certificate.pre PV_RunJoin_BankCell4619.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell4619.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell4620

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell4720
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell4719.certificate.pre) i +
    (liftA PV_RunJoin_BankCell4719.certificate.absorption) i else (liftA PV_RunJoin_BankCell4719.certificate.pre) i) = s_47_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 1 = s_47_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell4719.certificate.pre) (liftA PV_RunJoin_BankCell4719.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_47_1,round_47_2]
  exact round_47_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 2 = s_47_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_47_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_47_3 = s_47_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_47_3).trans round_47_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_47_4 = s_47_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_47_4).trans round_47_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 3 = s_47_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_47_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_47_5 = s_47_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_47_5).trans round_47_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_47_6 = s_47_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_47_6).trans round_47_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 4 = s_47_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_47_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_47_7 = s_47_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_47_7).trans round_47_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_47_8 = s_47_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_47_8).trans round_47_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 5 = s_47_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_47_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_47_9 = s_47_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_47_9).trans round_47_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_47_10 = s_47_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_47_10).trans round_47_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 6 = s_47_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_47_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_47_11 = s_47_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_47_11).trans round_47_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_47_12 = s_47_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_47_12).trans round_47_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 7 = s_47_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_47_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_47_13 = s_47_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_47_13).trans round_47_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_47_14 = s_47_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_47_14).trans round_47_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 8 = s_47_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_47_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_47_15 = s_47_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_47_15).trans round_47_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_47_16 = s_47_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_47_16).trans round_47_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 9 = s_47_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_47_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_47_17 = s_47_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_47_17).trans round_47_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_47_18 = s_47_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_47_18).trans round_47_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 10 = s_47_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_47_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_47_19 = s_47_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_47_19).trans round_47_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_47_20 = s_47_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_47_20).trans round_47_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) 11 = s_47_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_47_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_47_21 = s_47_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_47_21).trans round_47_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_47_22 = s_47_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_47_22).trans round_47_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell4719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell4719.canon3
  · exact PV_RunJoin_ValidatorCell4719.canon5
  · exact PV_RunJoin_ValidatorCell4719.canon7
  · exact PV_RunJoin_ValidatorCell4719.canon9
  · exact PV_RunJoin_ValidatorCell4719.canon11
  · exact PV_RunJoin_ValidatorCell4719.canon13
  · exact PV_RunJoin_ValidatorCell4719.canon15
  · exact PV_RunJoin_ValidatorCell4719.canon17
  · exact PV_RunJoin_ValidatorCell4719.canon19
  · exact PV_RunJoin_ValidatorCell4719.canon21
  · exact PV_RunJoin_ValidatorCell4719.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4719.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell4719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell4719.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell4719.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell4719.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell4719.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell4719.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell4719.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell4719.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell4719.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell4719.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell4719.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell4719.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell4719.certificate.pre PV_RunJoin_BankCell4719.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell4719.certificate.pre PV_RunJoin_BankCell4719.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell4719.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell4720

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell4820
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell4819.certificate.pre) i +
    (liftA PV_RunJoin_BankCell4819.certificate.absorption) i else (liftA PV_RunJoin_BankCell4819.certificate.pre) i) = s_48_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 1 = s_48_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell4819.certificate.pre) (liftA PV_RunJoin_BankCell4819.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_48_1,round_48_2]
  exact round_48_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 2 = s_48_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_48_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_48_3 = s_48_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_48_3).trans round_48_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_48_4 = s_48_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_48_4).trans round_48_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 3 = s_48_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_48_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_48_5 = s_48_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_48_5).trans round_48_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_48_6 = s_48_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_48_6).trans round_48_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 4 = s_48_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_48_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_48_7 = s_48_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_48_7).trans round_48_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_48_8 = s_48_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_48_8).trans round_48_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 5 = s_48_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_48_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_48_9 = s_48_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_48_9).trans round_48_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_48_10 = s_48_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_48_10).trans round_48_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 6 = s_48_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_48_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_48_11 = s_48_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_48_11).trans round_48_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_48_12 = s_48_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_48_12).trans round_48_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 7 = s_48_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_48_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_48_13 = s_48_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_48_13).trans round_48_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_48_14 = s_48_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_48_14).trans round_48_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 8 = s_48_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_48_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_48_15 = s_48_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_48_15).trans round_48_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_48_16 = s_48_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_48_16).trans round_48_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 9 = s_48_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_48_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_48_17 = s_48_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_48_17).trans round_48_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_48_18 = s_48_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_48_18).trans round_48_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 10 = s_48_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_48_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_48_19 = s_48_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_48_19).trans round_48_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_48_20 = s_48_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_48_20).trans round_48_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) 11 = s_48_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_48_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_48_21 = s_48_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_48_21).trans round_48_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_48_22 = s_48_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_48_22).trans round_48_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell4819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell4819.canon3
  · exact PV_RunJoin_ValidatorCell4819.canon5
  · exact PV_RunJoin_ValidatorCell4819.canon7
  · exact PV_RunJoin_ValidatorCell4819.canon9
  · exact PV_RunJoin_ValidatorCell4819.canon11
  · exact PV_RunJoin_ValidatorCell4819.canon13
  · exact PV_RunJoin_ValidatorCell4819.canon15
  · exact PV_RunJoin_ValidatorCell4819.canon17
  · exact PV_RunJoin_ValidatorCell4819.canon19
  · exact PV_RunJoin_ValidatorCell4819.canon21
  · exact PV_RunJoin_ValidatorCell4819.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4819.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell4819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell4819.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell4819.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell4819.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell4819.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell4819.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell4819.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell4819.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell4819.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell4819.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell4819.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell4819.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell4819.certificate.pre PV_RunJoin_BankCell4819.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell4819.certificate.pre PV_RunJoin_BankCell4819.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell4819.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell4820

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell4920
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell4919.certificate.pre) i +
    (liftA PV_RunJoin_BankCell4919.certificate.absorption) i else (liftA PV_RunJoin_BankCell4919.certificate.pre) i) = s_49_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 1 = s_49_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell4919.certificate.pre) (liftA PV_RunJoin_BankCell4919.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_49_1,round_49_2]
  exact round_49_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 2 = s_49_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_49_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_49_3 = s_49_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_49_3).trans round_49_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_49_4 = s_49_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_49_4).trans round_49_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 3 = s_49_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_49_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_49_5 = s_49_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_49_5).trans round_49_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_49_6 = s_49_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_49_6).trans round_49_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 4 = s_49_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_49_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_49_7 = s_49_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_49_7).trans round_49_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_49_8 = s_49_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_49_8).trans round_49_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 5 = s_49_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_49_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_49_9 = s_49_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_49_9).trans round_49_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_49_10 = s_49_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_49_10).trans round_49_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 6 = s_49_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_49_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_49_11 = s_49_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_49_11).trans round_49_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_49_12 = s_49_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_49_12).trans round_49_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 7 = s_49_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_49_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_49_13 = s_49_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_49_13).trans round_49_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_49_14 = s_49_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_49_14).trans round_49_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 8 = s_49_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_49_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_49_15 = s_49_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_49_15).trans round_49_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_49_16 = s_49_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_49_16).trans round_49_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 9 = s_49_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_49_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_49_17 = s_49_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_49_17).trans round_49_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_49_18 = s_49_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_49_18).trans round_49_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 10 = s_49_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_49_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_49_19 = s_49_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_49_19).trans round_49_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_49_20 = s_49_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_49_20).trans round_49_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) 11 = s_49_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_49_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_49_21 = s_49_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_49_21).trans round_49_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_49_22 = s_49_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_49_22).trans round_49_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell4919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell4919.canon3
  · exact PV_RunJoin_ValidatorCell4919.canon5
  · exact PV_RunJoin_ValidatorCell4919.canon7
  · exact PV_RunJoin_ValidatorCell4919.canon9
  · exact PV_RunJoin_ValidatorCell4919.canon11
  · exact PV_RunJoin_ValidatorCell4919.canon13
  · exact PV_RunJoin_ValidatorCell4919.canon15
  · exact PV_RunJoin_ValidatorCell4919.canon17
  · exact PV_RunJoin_ValidatorCell4919.canon19
  · exact PV_RunJoin_ValidatorCell4919.canon21
  · exact PV_RunJoin_ValidatorCell4919.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4919.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell4919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell4919.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell4919.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell4919.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell4919.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell4919.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell4919.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell4919.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell4919.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell4919.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell4919.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell4919.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell4919.certificate.pre PV_RunJoin_BankCell4919.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell4919.certificate.pre PV_RunJoin_BankCell4919.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell4919.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell4920

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell5020
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell5019.certificate.pre) i +
    (liftA PV_RunJoin_BankCell5019.certificate.absorption) i else (liftA PV_RunJoin_BankCell5019.certificate.pre) i) = s_50_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 1 = s_50_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell5019.certificate.pre) (liftA PV_RunJoin_BankCell5019.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_50_1,round_50_2]
  exact round_50_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 2 = s_50_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_50_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_50_3 = s_50_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_50_3).trans round_50_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_50_4 = s_50_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_50_4).trans round_50_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 3 = s_50_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_50_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_50_5 = s_50_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_50_5).trans round_50_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_50_6 = s_50_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_50_6).trans round_50_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 4 = s_50_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_50_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_50_7 = s_50_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_50_7).trans round_50_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_50_8 = s_50_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_50_8).trans round_50_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 5 = s_50_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_50_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_50_9 = s_50_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_50_9).trans round_50_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_50_10 = s_50_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_50_10).trans round_50_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 6 = s_50_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_50_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_50_11 = s_50_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_50_11).trans round_50_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_50_12 = s_50_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_50_12).trans round_50_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 7 = s_50_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_50_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_50_13 = s_50_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_50_13).trans round_50_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_50_14 = s_50_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_50_14).trans round_50_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 8 = s_50_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_50_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_50_15 = s_50_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_50_15).trans round_50_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_50_16 = s_50_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_50_16).trans round_50_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 9 = s_50_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_50_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_50_17 = s_50_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_50_17).trans round_50_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_50_18 = s_50_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_50_18).trans round_50_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 10 = s_50_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_50_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_50_19 = s_50_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_50_19).trans round_50_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_50_20 = s_50_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_50_20).trans round_50_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) 11 = s_50_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_50_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_50_21 = s_50_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_50_21).trans round_50_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_50_22 = s_50_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_50_22).trans round_50_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell5019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell5019.canon3
  · exact PV_RunJoin_ValidatorCell5019.canon5
  · exact PV_RunJoin_ValidatorCell5019.canon7
  · exact PV_RunJoin_ValidatorCell5019.canon9
  · exact PV_RunJoin_ValidatorCell5019.canon11
  · exact PV_RunJoin_ValidatorCell5019.canon13
  · exact PV_RunJoin_ValidatorCell5019.canon15
  · exact PV_RunJoin_ValidatorCell5019.canon17
  · exact PV_RunJoin_ValidatorCell5019.canon19
  · exact PV_RunJoin_ValidatorCell5019.canon21
  · exact PV_RunJoin_ValidatorCell5019.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5019.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell5019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell5019.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell5019.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell5019.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell5019.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell5019.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell5019.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell5019.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell5019.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell5019.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell5019.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell5019.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell5019.certificate.pre PV_RunJoin_BankCell5019.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell5019.certificate.pre PV_RunJoin_BankCell5019.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell5019.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell5020

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell5120
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell5119.certificate.pre) i +
    (liftA PV_RunJoin_BankCell5119.certificate.absorption) i else (liftA PV_RunJoin_BankCell5119.certificate.pre) i) = s_51_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 1 = s_51_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell5119.certificate.pre) (liftA PV_RunJoin_BankCell5119.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_51_1,round_51_2]
  exact round_51_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 2 = s_51_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_51_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_51_3 = s_51_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_51_3).trans round_51_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_51_4 = s_51_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_51_4).trans round_51_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 3 = s_51_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_51_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_51_5 = s_51_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_51_5).trans round_51_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_51_6 = s_51_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_51_6).trans round_51_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 4 = s_51_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_51_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_51_7 = s_51_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_51_7).trans round_51_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_51_8 = s_51_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_51_8).trans round_51_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 5 = s_51_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_51_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_51_9 = s_51_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_51_9).trans round_51_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_51_10 = s_51_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_51_10).trans round_51_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 6 = s_51_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_51_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_51_11 = s_51_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_51_11).trans round_51_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_51_12 = s_51_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_51_12).trans round_51_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 7 = s_51_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_51_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_51_13 = s_51_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_51_13).trans round_51_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_51_14 = s_51_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_51_14).trans round_51_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 8 = s_51_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_51_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_51_15 = s_51_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_51_15).trans round_51_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_51_16 = s_51_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_51_16).trans round_51_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 9 = s_51_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_51_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_51_17 = s_51_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_51_17).trans round_51_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_51_18 = s_51_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_51_18).trans round_51_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 10 = s_51_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_51_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_51_19 = s_51_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_51_19).trans round_51_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_51_20 = s_51_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_51_20).trans round_51_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) 11 = s_51_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_51_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_51_21 = s_51_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_51_21).trans round_51_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_51_22 = s_51_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_51_22).trans round_51_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell5119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell5119.canon3
  · exact PV_RunJoin_ValidatorCell5119.canon5
  · exact PV_RunJoin_ValidatorCell5119.canon7
  · exact PV_RunJoin_ValidatorCell5119.canon9
  · exact PV_RunJoin_ValidatorCell5119.canon11
  · exact PV_RunJoin_ValidatorCell5119.canon13
  · exact PV_RunJoin_ValidatorCell5119.canon15
  · exact PV_RunJoin_ValidatorCell5119.canon17
  · exact PV_RunJoin_ValidatorCell5119.canon19
  · exact PV_RunJoin_ValidatorCell5119.canon21
  · exact PV_RunJoin_ValidatorCell5119.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5119.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell5119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell5119.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell5119.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell5119.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell5119.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell5119.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell5119.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell5119.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell5119.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell5119.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell5119.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell5119.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell5119.certificate.pre PV_RunJoin_BankCell5119.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell5119.certificate.pre PV_RunJoin_BankCell5119.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell5119.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell5120

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell5220
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell5219.certificate.pre) i +
    (liftA PV_RunJoin_BankCell5219.certificate.absorption) i else (liftA PV_RunJoin_BankCell5219.certificate.pre) i) = s_52_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 1 = s_52_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell5219.certificate.pre) (liftA PV_RunJoin_BankCell5219.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_52_1,round_52_2]
  exact round_52_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 2 = s_52_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_52_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_52_3 = s_52_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_52_3).trans round_52_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_52_4 = s_52_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_52_4).trans round_52_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 3 = s_52_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_52_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_52_5 = s_52_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_52_5).trans round_52_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_52_6 = s_52_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_52_6).trans round_52_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 4 = s_52_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_52_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_52_7 = s_52_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_52_7).trans round_52_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_52_8 = s_52_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_52_8).trans round_52_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 5 = s_52_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_52_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_52_9 = s_52_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_52_9).trans round_52_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_52_10 = s_52_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_52_10).trans round_52_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 6 = s_52_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_52_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_52_11 = s_52_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_52_11).trans round_52_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_52_12 = s_52_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_52_12).trans round_52_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 7 = s_52_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_52_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_52_13 = s_52_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_52_13).trans round_52_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_52_14 = s_52_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_52_14).trans round_52_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 8 = s_52_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_52_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_52_15 = s_52_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_52_15).trans round_52_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_52_16 = s_52_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_52_16).trans round_52_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 9 = s_52_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_52_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_52_17 = s_52_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_52_17).trans round_52_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_52_18 = s_52_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_52_18).trans round_52_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 10 = s_52_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_52_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_52_19 = s_52_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_52_19).trans round_52_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_52_20 = s_52_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_52_20).trans round_52_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) 11 = s_52_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_52_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_52_21 = s_52_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_52_21).trans round_52_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_52_22 = s_52_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_52_22).trans round_52_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell5219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell5219.canon3
  · exact PV_RunJoin_ValidatorCell5219.canon5
  · exact PV_RunJoin_ValidatorCell5219.canon7
  · exact PV_RunJoin_ValidatorCell5219.canon9
  · exact PV_RunJoin_ValidatorCell5219.canon11
  · exact PV_RunJoin_ValidatorCell5219.canon13
  · exact PV_RunJoin_ValidatorCell5219.canon15
  · exact PV_RunJoin_ValidatorCell5219.canon17
  · exact PV_RunJoin_ValidatorCell5219.canon19
  · exact PV_RunJoin_ValidatorCell5219.canon21
  · exact PV_RunJoin_ValidatorCell5219.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5219.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell5219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell5219.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell5219.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell5219.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell5219.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell5219.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell5219.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell5219.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell5219.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell5219.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell5219.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell5219.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell5219.certificate.pre PV_RunJoin_BankCell5219.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell5219.certificate.pre PV_RunJoin_BankCell5219.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell5219.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell5220

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell5320
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell5319.certificate.pre) i +
    (liftA PV_RunJoin_BankCell5319.certificate.absorption) i else (liftA PV_RunJoin_BankCell5319.certificate.pre) i) = s_53_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 1 = s_53_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell5319.certificate.pre) (liftA PV_RunJoin_BankCell5319.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_53_1,round_53_2]
  exact round_53_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 2 = s_53_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_53_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_53_3 = s_53_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_53_3).trans round_53_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_53_4 = s_53_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_53_4).trans round_53_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 3 = s_53_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_53_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_53_5 = s_53_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_53_5).trans round_53_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_53_6 = s_53_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_53_6).trans round_53_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 4 = s_53_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_53_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_53_7 = s_53_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_53_7).trans round_53_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_53_8 = s_53_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_53_8).trans round_53_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 5 = s_53_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_53_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_53_9 = s_53_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_53_9).trans round_53_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_53_10 = s_53_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_53_10).trans round_53_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 6 = s_53_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_53_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_53_11 = s_53_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_53_11).trans round_53_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_53_12 = s_53_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_53_12).trans round_53_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 7 = s_53_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_53_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_53_13 = s_53_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_53_13).trans round_53_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_53_14 = s_53_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_53_14).trans round_53_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 8 = s_53_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_53_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_53_15 = s_53_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_53_15).trans round_53_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_53_16 = s_53_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_53_16).trans round_53_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 9 = s_53_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_53_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_53_17 = s_53_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_53_17).trans round_53_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_53_18 = s_53_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_53_18).trans round_53_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 10 = s_53_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_53_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_53_19 = s_53_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_53_19).trans round_53_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_53_20 = s_53_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_53_20).trans round_53_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) 11 = s_53_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_53_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_53_21 = s_53_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_53_21).trans round_53_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_53_22 = s_53_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_53_22).trans round_53_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell5319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell5319.canon3
  · exact PV_RunJoin_ValidatorCell5319.canon5
  · exact PV_RunJoin_ValidatorCell5319.canon7
  · exact PV_RunJoin_ValidatorCell5319.canon9
  · exact PV_RunJoin_ValidatorCell5319.canon11
  · exact PV_RunJoin_ValidatorCell5319.canon13
  · exact PV_RunJoin_ValidatorCell5319.canon15
  · exact PV_RunJoin_ValidatorCell5319.canon17
  · exact PV_RunJoin_ValidatorCell5319.canon19
  · exact PV_RunJoin_ValidatorCell5319.canon21
  · exact PV_RunJoin_ValidatorCell5319.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5319.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell5319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell5319.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell5319.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell5319.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell5319.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell5319.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell5319.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell5319.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell5319.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell5319.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell5319.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell5319.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell5319.certificate.pre PV_RunJoin_BankCell5319.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell5319.certificate.pre PV_RunJoin_BankCell5319.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell5319.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell5320
