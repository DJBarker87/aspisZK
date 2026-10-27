import R1Z.PV_RunJoin_CopyCertificate20
import R1Z.PV_RunJoin_BankCells6319
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell6320
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell6319.certificate.pre) i +
    (liftA PV_RunJoin_BankCell6319.certificate.absorption) i else (liftA PV_RunJoin_BankCell6319.certificate.pre) i) = s_63_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 1 = s_63_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell6319.certificate.pre) (liftA PV_RunJoin_BankCell6319.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_63_1,round_63_2]
  exact round_63_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 2 = s_63_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_63_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_63_3 = s_63_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_63_3).trans round_63_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_63_4 = s_63_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_63_4).trans round_63_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 3 = s_63_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_63_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_63_5 = s_63_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_63_5).trans round_63_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_63_6 = s_63_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_63_6).trans round_63_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 4 = s_63_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_63_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_63_7 = s_63_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_63_7).trans round_63_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_63_8 = s_63_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_63_8).trans round_63_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 5 = s_63_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_63_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_63_9 = s_63_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_63_9).trans round_63_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_63_10 = s_63_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_63_10).trans round_63_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 6 = s_63_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_63_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_63_11 = s_63_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_63_11).trans round_63_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_63_12 = s_63_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_63_12).trans round_63_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 7 = s_63_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_63_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_63_13 = s_63_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_63_13).trans round_63_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_63_14 = s_63_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_63_14).trans round_63_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 8 = s_63_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_63_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_63_15 = s_63_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_63_15).trans round_63_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_63_16 = s_63_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_63_16).trans round_63_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 9 = s_63_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_63_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_63_17 = s_63_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_63_17).trans round_63_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_63_18 = s_63_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_63_18).trans round_63_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 10 = s_63_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_63_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_63_19 = s_63_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_63_19).trans round_63_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_63_20 = s_63_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_63_20).trans round_63_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) 11 = s_63_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_63_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_63_21 = s_63_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_63_21).trans round_63_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_63_22 = s_63_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_63_22).trans round_63_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell6319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell6319.canon3
  · exact PV_RunJoin_ValidatorCell6319.canon5
  · exact PV_RunJoin_ValidatorCell6319.canon7
  · exact PV_RunJoin_ValidatorCell6319.canon9
  · exact PV_RunJoin_ValidatorCell6319.canon11
  · exact PV_RunJoin_ValidatorCell6319.canon13
  · exact PV_RunJoin_ValidatorCell6319.canon15
  · exact PV_RunJoin_ValidatorCell6319.canon17
  · exact PV_RunJoin_ValidatorCell6319.canon19
  · exact PV_RunJoin_ValidatorCell6319.canon21
  · exact PV_RunJoin_ValidatorCell6319.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6319.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell6319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell6319.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell6319.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell6319.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell6319.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell6319.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell6319.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell6319.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell6319.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell6319.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell6319.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell6319.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell6319.certificate.pre PV_RunJoin_BankCell6319.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell6319.certificate.pre PV_RunJoin_BankCell6319.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell6319.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell6320

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell6420
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell6419.certificate.pre) i +
    (liftA PV_RunJoin_BankCell6419.certificate.absorption) i else (liftA PV_RunJoin_BankCell6419.certificate.pre) i) = s_64_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 1 = s_64_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell6419.certificate.pre) (liftA PV_RunJoin_BankCell6419.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_64_1,round_64_2]
  exact round_64_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 2 = s_64_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_64_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_64_3 = s_64_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_64_3).trans round_64_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_64_4 = s_64_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_64_4).trans round_64_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 3 = s_64_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_64_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_64_5 = s_64_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_64_5).trans round_64_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_64_6 = s_64_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_64_6).trans round_64_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 4 = s_64_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_64_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_64_7 = s_64_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_64_7).trans round_64_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_64_8 = s_64_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_64_8).trans round_64_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 5 = s_64_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_64_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_64_9 = s_64_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_64_9).trans round_64_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_64_10 = s_64_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_64_10).trans round_64_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 6 = s_64_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_64_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_64_11 = s_64_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_64_11).trans round_64_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_64_12 = s_64_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_64_12).trans round_64_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 7 = s_64_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_64_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_64_13 = s_64_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_64_13).trans round_64_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_64_14 = s_64_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_64_14).trans round_64_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 8 = s_64_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_64_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_64_15 = s_64_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_64_15).trans round_64_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_64_16 = s_64_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_64_16).trans round_64_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 9 = s_64_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_64_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_64_17 = s_64_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_64_17).trans round_64_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_64_18 = s_64_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_64_18).trans round_64_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 10 = s_64_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_64_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_64_19 = s_64_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_64_19).trans round_64_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_64_20 = s_64_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_64_20).trans round_64_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) 11 = s_64_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_64_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_64_21 = s_64_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_64_21).trans round_64_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_64_22 = s_64_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_64_22).trans round_64_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell6419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell6419.canon3
  · exact PV_RunJoin_ValidatorCell6419.canon5
  · exact PV_RunJoin_ValidatorCell6419.canon7
  · exact PV_RunJoin_ValidatorCell6419.canon9
  · exact PV_RunJoin_ValidatorCell6419.canon11
  · exact PV_RunJoin_ValidatorCell6419.canon13
  · exact PV_RunJoin_ValidatorCell6419.canon15
  · exact PV_RunJoin_ValidatorCell6419.canon17
  · exact PV_RunJoin_ValidatorCell6419.canon19
  · exact PV_RunJoin_ValidatorCell6419.canon21
  · exact PV_RunJoin_ValidatorCell6419.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6419.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell6419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell6419.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell6419.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell6419.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell6419.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell6419.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell6419.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell6419.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell6419.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell6419.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell6419.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell6419.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell6419.certificate.pre PV_RunJoin_BankCell6419.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell6419.certificate.pre PV_RunJoin_BankCell6419.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell6419.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell6420

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell6520
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell6519.certificate.pre) i +
    (liftA PV_RunJoin_BankCell6519.certificate.absorption) i else (liftA PV_RunJoin_BankCell6519.certificate.pre) i) = s_65_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 1 = s_65_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell6519.certificate.pre) (liftA PV_RunJoin_BankCell6519.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_65_1,round_65_2]
  exact round_65_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 2 = s_65_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_65_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_65_3 = s_65_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_65_3).trans round_65_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_65_4 = s_65_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_65_4).trans round_65_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 3 = s_65_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_65_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_65_5 = s_65_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_65_5).trans round_65_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_65_6 = s_65_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_65_6).trans round_65_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 4 = s_65_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_65_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_65_7 = s_65_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_65_7).trans round_65_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_65_8 = s_65_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_65_8).trans round_65_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 5 = s_65_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_65_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_65_9 = s_65_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_65_9).trans round_65_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_65_10 = s_65_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_65_10).trans round_65_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 6 = s_65_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_65_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_65_11 = s_65_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_65_11).trans round_65_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_65_12 = s_65_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_65_12).trans round_65_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 7 = s_65_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_65_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_65_13 = s_65_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_65_13).trans round_65_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_65_14 = s_65_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_65_14).trans round_65_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 8 = s_65_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_65_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_65_15 = s_65_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_65_15).trans round_65_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_65_16 = s_65_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_65_16).trans round_65_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 9 = s_65_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_65_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_65_17 = s_65_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_65_17).trans round_65_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_65_18 = s_65_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_65_18).trans round_65_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 10 = s_65_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_65_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_65_19 = s_65_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_65_19).trans round_65_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_65_20 = s_65_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_65_20).trans round_65_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) 11 = s_65_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_65_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_65_21 = s_65_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_65_21).trans round_65_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_65_22 = s_65_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_65_22).trans round_65_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell6519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell6519.canon3
  · exact PV_RunJoin_ValidatorCell6519.canon5
  · exact PV_RunJoin_ValidatorCell6519.canon7
  · exact PV_RunJoin_ValidatorCell6519.canon9
  · exact PV_RunJoin_ValidatorCell6519.canon11
  · exact PV_RunJoin_ValidatorCell6519.canon13
  · exact PV_RunJoin_ValidatorCell6519.canon15
  · exact PV_RunJoin_ValidatorCell6519.canon17
  · exact PV_RunJoin_ValidatorCell6519.canon19
  · exact PV_RunJoin_ValidatorCell6519.canon21
  · exact PV_RunJoin_ValidatorCell6519.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6519.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell6519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell6519.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell6519.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell6519.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell6519.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell6519.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell6519.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell6519.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell6519.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell6519.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell6519.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell6519.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell6519.certificate.pre PV_RunJoin_BankCell6519.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell6519.certificate.pre PV_RunJoin_BankCell6519.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell6519.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell6520

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell6620
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell6619.certificate.pre) i +
    (liftA PV_RunJoin_BankCell6619.certificate.absorption) i else (liftA PV_RunJoin_BankCell6619.certificate.pre) i) = s_66_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 1 = s_66_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell6619.certificate.pre) (liftA PV_RunJoin_BankCell6619.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_66_1,round_66_2]
  exact round_66_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 2 = s_66_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_66_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_66_3 = s_66_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_66_3).trans round_66_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_66_4 = s_66_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_66_4).trans round_66_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 3 = s_66_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_66_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_66_5 = s_66_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_66_5).trans round_66_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_66_6 = s_66_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_66_6).trans round_66_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 4 = s_66_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_66_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_66_7 = s_66_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_66_7).trans round_66_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_66_8 = s_66_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_66_8).trans round_66_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 5 = s_66_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_66_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_66_9 = s_66_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_66_9).trans round_66_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_66_10 = s_66_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_66_10).trans round_66_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 6 = s_66_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_66_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_66_11 = s_66_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_66_11).trans round_66_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_66_12 = s_66_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_66_12).trans round_66_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 7 = s_66_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_66_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_66_13 = s_66_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_66_13).trans round_66_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_66_14 = s_66_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_66_14).trans round_66_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 8 = s_66_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_66_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_66_15 = s_66_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_66_15).trans round_66_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_66_16 = s_66_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_66_16).trans round_66_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 9 = s_66_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_66_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_66_17 = s_66_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_66_17).trans round_66_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_66_18 = s_66_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_66_18).trans round_66_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 10 = s_66_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_66_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_66_19 = s_66_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_66_19).trans round_66_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_66_20 = s_66_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_66_20).trans round_66_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) 11 = s_66_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_66_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_66_21 = s_66_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_66_21).trans round_66_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_66_22 = s_66_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_66_22).trans round_66_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell6619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell6619.canon3
  · exact PV_RunJoin_ValidatorCell6619.canon5
  · exact PV_RunJoin_ValidatorCell6619.canon7
  · exact PV_RunJoin_ValidatorCell6619.canon9
  · exact PV_RunJoin_ValidatorCell6619.canon11
  · exact PV_RunJoin_ValidatorCell6619.canon13
  · exact PV_RunJoin_ValidatorCell6619.canon15
  · exact PV_RunJoin_ValidatorCell6619.canon17
  · exact PV_RunJoin_ValidatorCell6619.canon19
  · exact PV_RunJoin_ValidatorCell6619.canon21
  · exact PV_RunJoin_ValidatorCell6619.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6619.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell6619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell6619.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell6619.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell6619.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell6619.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell6619.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell6619.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell6619.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell6619.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell6619.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell6619.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell6619.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell6619.certificate.pre PV_RunJoin_BankCell6619.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell6619.certificate.pre PV_RunJoin_BankCell6619.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell6619.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell6620

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell6720
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell6719.certificate.pre) i +
    (liftA PV_RunJoin_BankCell6719.certificate.absorption) i else (liftA PV_RunJoin_BankCell6719.certificate.pre) i) = s_67_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 1 = s_67_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell6719.certificate.pre) (liftA PV_RunJoin_BankCell6719.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_67_1,round_67_2]
  exact round_67_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 2 = s_67_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_67_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_67_3 = s_67_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_67_3).trans round_67_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_67_4 = s_67_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_67_4).trans round_67_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 3 = s_67_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_67_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_67_5 = s_67_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_67_5).trans round_67_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_67_6 = s_67_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_67_6).trans round_67_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 4 = s_67_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_67_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_67_7 = s_67_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_67_7).trans round_67_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_67_8 = s_67_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_67_8).trans round_67_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 5 = s_67_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_67_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_67_9 = s_67_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_67_9).trans round_67_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_67_10 = s_67_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_67_10).trans round_67_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 6 = s_67_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_67_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_67_11 = s_67_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_67_11).trans round_67_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_67_12 = s_67_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_67_12).trans round_67_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 7 = s_67_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_67_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_67_13 = s_67_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_67_13).trans round_67_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_67_14 = s_67_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_67_14).trans round_67_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 8 = s_67_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_67_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_67_15 = s_67_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_67_15).trans round_67_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_67_16 = s_67_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_67_16).trans round_67_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 9 = s_67_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_67_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_67_17 = s_67_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_67_17).trans round_67_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_67_18 = s_67_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_67_18).trans round_67_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 10 = s_67_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_67_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_67_19 = s_67_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_67_19).trans round_67_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_67_20 = s_67_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_67_20).trans round_67_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) 11 = s_67_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_67_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_67_21 = s_67_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_67_21).trans round_67_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_67_22 = s_67_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_67_22).trans round_67_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell6719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell6719.canon3
  · exact PV_RunJoin_ValidatorCell6719.canon5
  · exact PV_RunJoin_ValidatorCell6719.canon7
  · exact PV_RunJoin_ValidatorCell6719.canon9
  · exact PV_RunJoin_ValidatorCell6719.canon11
  · exact PV_RunJoin_ValidatorCell6719.canon13
  · exact PV_RunJoin_ValidatorCell6719.canon15
  · exact PV_RunJoin_ValidatorCell6719.canon17
  · exact PV_RunJoin_ValidatorCell6719.canon19
  · exact PV_RunJoin_ValidatorCell6719.canon21
  · exact PV_RunJoin_ValidatorCell6719.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6719.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell6719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell6719.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell6719.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell6719.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell6719.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell6719.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell6719.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell6719.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell6719.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell6719.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell6719.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell6719.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell6719.certificate.pre PV_RunJoin_BankCell6719.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell6719.certificate.pre PV_RunJoin_BankCell6719.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell6719.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell6720

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell6820
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell6819.certificate.pre) i +
    (liftA PV_RunJoin_BankCell6819.certificate.absorption) i else (liftA PV_RunJoin_BankCell6819.certificate.pre) i) = s_68_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 1 = s_68_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell6819.certificate.pre) (liftA PV_RunJoin_BankCell6819.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_68_1,round_68_2]
  exact round_68_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 2 = s_68_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_68_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_68_3 = s_68_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_68_3).trans round_68_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_68_4 = s_68_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_68_4).trans round_68_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 3 = s_68_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_68_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_68_5 = s_68_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_68_5).trans round_68_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_68_6 = s_68_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_68_6).trans round_68_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 4 = s_68_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_68_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_68_7 = s_68_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_68_7).trans round_68_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_68_8 = s_68_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_68_8).trans round_68_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 5 = s_68_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_68_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_68_9 = s_68_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_68_9).trans round_68_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_68_10 = s_68_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_68_10).trans round_68_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 6 = s_68_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_68_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_68_11 = s_68_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_68_11).trans round_68_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_68_12 = s_68_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_68_12).trans round_68_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 7 = s_68_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_68_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_68_13 = s_68_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_68_13).trans round_68_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_68_14 = s_68_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_68_14).trans round_68_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 8 = s_68_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_68_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_68_15 = s_68_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_68_15).trans round_68_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_68_16 = s_68_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_68_16).trans round_68_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 9 = s_68_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_68_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_68_17 = s_68_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_68_17).trans round_68_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_68_18 = s_68_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_68_18).trans round_68_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 10 = s_68_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_68_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_68_19 = s_68_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_68_19).trans round_68_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_68_20 = s_68_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_68_20).trans round_68_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) 11 = s_68_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_68_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_68_21 = s_68_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_68_21).trans round_68_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_68_22 = s_68_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_68_22).trans round_68_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell6819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell6819.canon3
  · exact PV_RunJoin_ValidatorCell6819.canon5
  · exact PV_RunJoin_ValidatorCell6819.canon7
  · exact PV_RunJoin_ValidatorCell6819.canon9
  · exact PV_RunJoin_ValidatorCell6819.canon11
  · exact PV_RunJoin_ValidatorCell6819.canon13
  · exact PV_RunJoin_ValidatorCell6819.canon15
  · exact PV_RunJoin_ValidatorCell6819.canon17
  · exact PV_RunJoin_ValidatorCell6819.canon19
  · exact PV_RunJoin_ValidatorCell6819.canon21
  · exact PV_RunJoin_ValidatorCell6819.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6819.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell6819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell6819.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell6819.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell6819.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell6819.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell6819.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell6819.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell6819.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell6819.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell6819.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell6819.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell6819.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell6819.certificate.pre PV_RunJoin_BankCell6819.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell6819.certificate.pre PV_RunJoin_BankCell6819.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell6819.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell6820

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell6920
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell6919.certificate.pre) i +
    (liftA PV_RunJoin_BankCell6919.certificate.absorption) i else (liftA PV_RunJoin_BankCell6919.certificate.pre) i) = s_69_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 1 = s_69_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell6919.certificate.pre) (liftA PV_RunJoin_BankCell6919.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_69_1,round_69_2]
  exact round_69_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 2 = s_69_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_69_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_69_3 = s_69_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_69_3).trans round_69_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_69_4 = s_69_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_69_4).trans round_69_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 3 = s_69_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_69_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_69_5 = s_69_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_69_5).trans round_69_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_69_6 = s_69_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_69_6).trans round_69_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 4 = s_69_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_69_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_69_7 = s_69_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_69_7).trans round_69_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_69_8 = s_69_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_69_8).trans round_69_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 5 = s_69_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_69_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_69_9 = s_69_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_69_9).trans round_69_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_69_10 = s_69_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_69_10).trans round_69_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 6 = s_69_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_69_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_69_11 = s_69_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_69_11).trans round_69_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_69_12 = s_69_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_69_12).trans round_69_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 7 = s_69_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_69_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_69_13 = s_69_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_69_13).trans round_69_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_69_14 = s_69_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_69_14).trans round_69_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 8 = s_69_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_69_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_69_15 = s_69_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_69_15).trans round_69_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_69_16 = s_69_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_69_16).trans round_69_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 9 = s_69_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_69_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_69_17 = s_69_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_69_17).trans round_69_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_69_18 = s_69_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_69_18).trans round_69_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 10 = s_69_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_69_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_69_19 = s_69_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_69_19).trans round_69_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_69_20 = s_69_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_69_20).trans round_69_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) 11 = s_69_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_69_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_69_21 = s_69_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_69_21).trans round_69_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_69_22 = s_69_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_69_22).trans round_69_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell6919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell6919.canon3
  · exact PV_RunJoin_ValidatorCell6919.canon5
  · exact PV_RunJoin_ValidatorCell6919.canon7
  · exact PV_RunJoin_ValidatorCell6919.canon9
  · exact PV_RunJoin_ValidatorCell6919.canon11
  · exact PV_RunJoin_ValidatorCell6919.canon13
  · exact PV_RunJoin_ValidatorCell6919.canon15
  · exact PV_RunJoin_ValidatorCell6919.canon17
  · exact PV_RunJoin_ValidatorCell6919.canon19
  · exact PV_RunJoin_ValidatorCell6919.canon21
  · exact PV_RunJoin_ValidatorCell6919.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6919.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell6919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell6919.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell6919.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell6919.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell6919.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell6919.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell6919.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell6919.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell6919.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell6919.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell6919.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell6919.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell6919.certificate.pre PV_RunJoin_BankCell6919.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell6919.certificate.pre PV_RunJoin_BankCell6919.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell6919.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell6920

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell7020
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell7019.certificate.pre) i +
    (liftA PV_RunJoin_BankCell7019.certificate.absorption) i else (liftA PV_RunJoin_BankCell7019.certificate.pre) i) = s_70_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 1 = s_70_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell7019.certificate.pre) (liftA PV_RunJoin_BankCell7019.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_70_1,round_70_2]
  exact round_70_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 2 = s_70_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_70_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_70_3 = s_70_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_70_3).trans round_70_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_70_4 = s_70_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_70_4).trans round_70_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 3 = s_70_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_70_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_70_5 = s_70_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_70_5).trans round_70_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_70_6 = s_70_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_70_6).trans round_70_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 4 = s_70_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_70_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_70_7 = s_70_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_70_7).trans round_70_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_70_8 = s_70_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_70_8).trans round_70_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 5 = s_70_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_70_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_70_9 = s_70_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_70_9).trans round_70_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_70_10 = s_70_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_70_10).trans round_70_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 6 = s_70_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_70_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_70_11 = s_70_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_70_11).trans round_70_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_70_12 = s_70_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_70_12).trans round_70_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 7 = s_70_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_70_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_70_13 = s_70_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_70_13).trans round_70_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_70_14 = s_70_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_70_14).trans round_70_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 8 = s_70_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_70_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_70_15 = s_70_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_70_15).trans round_70_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_70_16 = s_70_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_70_16).trans round_70_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 9 = s_70_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_70_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_70_17 = s_70_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_70_17).trans round_70_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_70_18 = s_70_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_70_18).trans round_70_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 10 = s_70_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_70_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_70_19 = s_70_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_70_19).trans round_70_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_70_20 = s_70_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_70_20).trans round_70_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) 11 = s_70_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_70_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_70_21 = s_70_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_70_21).trans round_70_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_70_22 = s_70_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_70_22).trans round_70_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell7019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell7019.canon3
  · exact PV_RunJoin_ValidatorCell7019.canon5
  · exact PV_RunJoin_ValidatorCell7019.canon7
  · exact PV_RunJoin_ValidatorCell7019.canon9
  · exact PV_RunJoin_ValidatorCell7019.canon11
  · exact PV_RunJoin_ValidatorCell7019.canon13
  · exact PV_RunJoin_ValidatorCell7019.canon15
  · exact PV_RunJoin_ValidatorCell7019.canon17
  · exact PV_RunJoin_ValidatorCell7019.canon19
  · exact PV_RunJoin_ValidatorCell7019.canon21
  · exact PV_RunJoin_ValidatorCell7019.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7019.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell7019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell7019.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell7019.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell7019.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell7019.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell7019.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell7019.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell7019.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell7019.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell7019.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell7019.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell7019.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell7019.certificate.pre PV_RunJoin_BankCell7019.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell7019.certificate.pre PV_RunJoin_BankCell7019.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell7019.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell7020

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell7120
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell7119.certificate.pre) i +
    (liftA PV_RunJoin_BankCell7119.certificate.absorption) i else (liftA PV_RunJoin_BankCell7119.certificate.pre) i) = s_71_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 1 = s_71_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell7119.certificate.pre) (liftA PV_RunJoin_BankCell7119.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_71_1,round_71_2]
  exact round_71_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 2 = s_71_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_71_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_71_3 = s_71_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_71_3).trans round_71_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_71_4 = s_71_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_71_4).trans round_71_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 3 = s_71_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_71_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_71_5 = s_71_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_71_5).trans round_71_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_71_6 = s_71_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_71_6).trans round_71_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 4 = s_71_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_71_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_71_7 = s_71_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_71_7).trans round_71_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_71_8 = s_71_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_71_8).trans round_71_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 5 = s_71_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_71_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_71_9 = s_71_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_71_9).trans round_71_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_71_10 = s_71_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_71_10).trans round_71_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 6 = s_71_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_71_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_71_11 = s_71_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_71_11).trans round_71_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_71_12 = s_71_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_71_12).trans round_71_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 7 = s_71_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_71_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_71_13 = s_71_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_71_13).trans round_71_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_71_14 = s_71_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_71_14).trans round_71_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 8 = s_71_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_71_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_71_15 = s_71_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_71_15).trans round_71_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_71_16 = s_71_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_71_16).trans round_71_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 9 = s_71_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_71_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_71_17 = s_71_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_71_17).trans round_71_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_71_18 = s_71_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_71_18).trans round_71_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 10 = s_71_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_71_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_71_19 = s_71_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_71_19).trans round_71_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_71_20 = s_71_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_71_20).trans round_71_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) 11 = s_71_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_71_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_71_21 = s_71_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_71_21).trans round_71_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_71_22 = s_71_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_71_22).trans round_71_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell7119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell7119.canon3
  · exact PV_RunJoin_ValidatorCell7119.canon5
  · exact PV_RunJoin_ValidatorCell7119.canon7
  · exact PV_RunJoin_ValidatorCell7119.canon9
  · exact PV_RunJoin_ValidatorCell7119.canon11
  · exact PV_RunJoin_ValidatorCell7119.canon13
  · exact PV_RunJoin_ValidatorCell7119.canon15
  · exact PV_RunJoin_ValidatorCell7119.canon17
  · exact PV_RunJoin_ValidatorCell7119.canon19
  · exact PV_RunJoin_ValidatorCell7119.canon21
  · exact PV_RunJoin_ValidatorCell7119.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7119.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell7119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell7119.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell7119.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell7119.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell7119.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell7119.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell7119.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell7119.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell7119.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell7119.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell7119.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell7119.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell7119.certificate.pre PV_RunJoin_BankCell7119.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell7119.certificate.pre PV_RunJoin_BankCell7119.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell7119.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell7120
