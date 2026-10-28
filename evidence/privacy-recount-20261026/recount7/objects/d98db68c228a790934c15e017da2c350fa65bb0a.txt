import R1Z.PV_RunJoin_CopyCertificate20
import R1Z.PV_RunJoin_BankCells3619
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell3620
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell3619.certificate.pre) i +
    (liftA PV_RunJoin_BankCell3619.certificate.absorption) i else (liftA PV_RunJoin_BankCell3619.certificate.pre) i) = s_36_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 1 = s_36_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell3619.certificate.pre) (liftA PV_RunJoin_BankCell3619.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_36_1,round_36_2]
  exact round_36_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 2 = s_36_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_36_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_36_3 = s_36_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_36_3).trans round_36_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_36_4 = s_36_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_36_4).trans round_36_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 3 = s_36_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_36_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_36_5 = s_36_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_36_5).trans round_36_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_36_6 = s_36_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_36_6).trans round_36_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 4 = s_36_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_36_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_36_7 = s_36_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_36_7).trans round_36_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_36_8 = s_36_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_36_8).trans round_36_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 5 = s_36_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_36_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_36_9 = s_36_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_36_9).trans round_36_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_36_10 = s_36_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_36_10).trans round_36_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 6 = s_36_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_36_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_36_11 = s_36_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_36_11).trans round_36_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_36_12 = s_36_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_36_12).trans round_36_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 7 = s_36_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_36_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_36_13 = s_36_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_36_13).trans round_36_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_36_14 = s_36_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_36_14).trans round_36_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 8 = s_36_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_36_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_36_15 = s_36_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_36_15).trans round_36_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_36_16 = s_36_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_36_16).trans round_36_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 9 = s_36_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_36_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_36_17 = s_36_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_36_17).trans round_36_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_36_18 = s_36_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_36_18).trans round_36_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 10 = s_36_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_36_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_36_19 = s_36_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_36_19).trans round_36_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_36_20 = s_36_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_36_20).trans round_36_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) 11 = s_36_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_36_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_36_21 = s_36_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_36_21).trans round_36_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_36_22 = s_36_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_36_22).trans round_36_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell3619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell3619.canon3
  · exact PV_RunJoin_ValidatorCell3619.canon5
  · exact PV_RunJoin_ValidatorCell3619.canon7
  · exact PV_RunJoin_ValidatorCell3619.canon9
  · exact PV_RunJoin_ValidatorCell3619.canon11
  · exact PV_RunJoin_ValidatorCell3619.canon13
  · exact PV_RunJoin_ValidatorCell3619.canon15
  · exact PV_RunJoin_ValidatorCell3619.canon17
  · exact PV_RunJoin_ValidatorCell3619.canon19
  · exact PV_RunJoin_ValidatorCell3619.canon21
  · exact PV_RunJoin_ValidatorCell3619.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3619.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell3619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell3619.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell3619.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell3619.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell3619.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell3619.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell3619.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell3619.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell3619.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell3619.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell3619.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell3619.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell3619.certificate.pre PV_RunJoin_BankCell3619.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell3619.certificate.pre PV_RunJoin_BankCell3619.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell3619.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell3620

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell3720
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell3719.certificate.pre) i +
    (liftA PV_RunJoin_BankCell3719.certificate.absorption) i else (liftA PV_RunJoin_BankCell3719.certificate.pre) i) = s_37_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 1 = s_37_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell3719.certificate.pre) (liftA PV_RunJoin_BankCell3719.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_37_1,round_37_2]
  exact round_37_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 2 = s_37_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_37_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_37_3 = s_37_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_37_3).trans round_37_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_37_4 = s_37_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_37_4).trans round_37_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 3 = s_37_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_37_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_37_5 = s_37_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_37_5).trans round_37_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_37_6 = s_37_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_37_6).trans round_37_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 4 = s_37_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_37_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_37_7 = s_37_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_37_7).trans round_37_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_37_8 = s_37_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_37_8).trans round_37_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 5 = s_37_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_37_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_37_9 = s_37_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_37_9).trans round_37_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_37_10 = s_37_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_37_10).trans round_37_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 6 = s_37_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_37_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_37_11 = s_37_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_37_11).trans round_37_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_37_12 = s_37_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_37_12).trans round_37_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 7 = s_37_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_37_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_37_13 = s_37_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_37_13).trans round_37_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_37_14 = s_37_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_37_14).trans round_37_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 8 = s_37_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_37_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_37_15 = s_37_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_37_15).trans round_37_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_37_16 = s_37_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_37_16).trans round_37_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 9 = s_37_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_37_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_37_17 = s_37_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_37_17).trans round_37_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_37_18 = s_37_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_37_18).trans round_37_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 10 = s_37_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_37_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_37_19 = s_37_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_37_19).trans round_37_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_37_20 = s_37_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_37_20).trans round_37_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) 11 = s_37_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_37_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_37_21 = s_37_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_37_21).trans round_37_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_37_22 = s_37_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_37_22).trans round_37_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell3719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell3719.canon3
  · exact PV_RunJoin_ValidatorCell3719.canon5
  · exact PV_RunJoin_ValidatorCell3719.canon7
  · exact PV_RunJoin_ValidatorCell3719.canon9
  · exact PV_RunJoin_ValidatorCell3719.canon11
  · exact PV_RunJoin_ValidatorCell3719.canon13
  · exact PV_RunJoin_ValidatorCell3719.canon15
  · exact PV_RunJoin_ValidatorCell3719.canon17
  · exact PV_RunJoin_ValidatorCell3719.canon19
  · exact PV_RunJoin_ValidatorCell3719.canon21
  · exact PV_RunJoin_ValidatorCell3719.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3719.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell3719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell3719.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell3719.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell3719.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell3719.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell3719.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell3719.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell3719.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell3719.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell3719.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell3719.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell3719.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell3719.certificate.pre PV_RunJoin_BankCell3719.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell3719.certificate.pre PV_RunJoin_BankCell3719.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell3719.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell3720

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell3820
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell3819.certificate.pre) i +
    (liftA PV_RunJoin_BankCell3819.certificate.absorption) i else (liftA PV_RunJoin_BankCell3819.certificate.pre) i) = s_38_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 1 = s_38_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell3819.certificate.pre) (liftA PV_RunJoin_BankCell3819.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_38_1,round_38_2]
  exact round_38_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 2 = s_38_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_38_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_38_3 = s_38_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_38_3).trans round_38_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_38_4 = s_38_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_38_4).trans round_38_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 3 = s_38_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_38_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_38_5 = s_38_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_38_5).trans round_38_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_38_6 = s_38_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_38_6).trans round_38_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 4 = s_38_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_38_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_38_7 = s_38_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_38_7).trans round_38_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_38_8 = s_38_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_38_8).trans round_38_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 5 = s_38_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_38_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_38_9 = s_38_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_38_9).trans round_38_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_38_10 = s_38_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_38_10).trans round_38_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 6 = s_38_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_38_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_38_11 = s_38_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_38_11).trans round_38_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_38_12 = s_38_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_38_12).trans round_38_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 7 = s_38_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_38_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_38_13 = s_38_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_38_13).trans round_38_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_38_14 = s_38_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_38_14).trans round_38_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 8 = s_38_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_38_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_38_15 = s_38_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_38_15).trans round_38_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_38_16 = s_38_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_38_16).trans round_38_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 9 = s_38_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_38_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_38_17 = s_38_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_38_17).trans round_38_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_38_18 = s_38_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_38_18).trans round_38_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 10 = s_38_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_38_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_38_19 = s_38_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_38_19).trans round_38_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_38_20 = s_38_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_38_20).trans round_38_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) 11 = s_38_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_38_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_38_21 = s_38_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_38_21).trans round_38_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_38_22 = s_38_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_38_22).trans round_38_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell3819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell3819.canon3
  · exact PV_RunJoin_ValidatorCell3819.canon5
  · exact PV_RunJoin_ValidatorCell3819.canon7
  · exact PV_RunJoin_ValidatorCell3819.canon9
  · exact PV_RunJoin_ValidatorCell3819.canon11
  · exact PV_RunJoin_ValidatorCell3819.canon13
  · exact PV_RunJoin_ValidatorCell3819.canon15
  · exact PV_RunJoin_ValidatorCell3819.canon17
  · exact PV_RunJoin_ValidatorCell3819.canon19
  · exact PV_RunJoin_ValidatorCell3819.canon21
  · exact PV_RunJoin_ValidatorCell3819.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3819.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell3819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell3819.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell3819.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell3819.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell3819.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell3819.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell3819.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell3819.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell3819.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell3819.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell3819.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell3819.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell3819.certificate.pre PV_RunJoin_BankCell3819.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell3819.certificate.pre PV_RunJoin_BankCell3819.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell3819.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell3820

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell3920
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell3919.certificate.pre) i +
    (liftA PV_RunJoin_BankCell3919.certificate.absorption) i else (liftA PV_RunJoin_BankCell3919.certificate.pre) i) = s_39_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 1 = s_39_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell3919.certificate.pre) (liftA PV_RunJoin_BankCell3919.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_39_1,round_39_2]
  exact round_39_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 2 = s_39_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_39_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_39_3 = s_39_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_39_3).trans round_39_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_39_4 = s_39_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_39_4).trans round_39_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 3 = s_39_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_39_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_39_5 = s_39_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_39_5).trans round_39_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_39_6 = s_39_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_39_6).trans round_39_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 4 = s_39_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_39_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_39_7 = s_39_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_39_7).trans round_39_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_39_8 = s_39_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_39_8).trans round_39_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 5 = s_39_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_39_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_39_9 = s_39_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_39_9).trans round_39_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_39_10 = s_39_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_39_10).trans round_39_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 6 = s_39_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_39_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_39_11 = s_39_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_39_11).trans round_39_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_39_12 = s_39_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_39_12).trans round_39_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 7 = s_39_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_39_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_39_13 = s_39_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_39_13).trans round_39_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_39_14 = s_39_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_39_14).trans round_39_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 8 = s_39_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_39_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_39_15 = s_39_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_39_15).trans round_39_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_39_16 = s_39_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_39_16).trans round_39_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 9 = s_39_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_39_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_39_17 = s_39_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_39_17).trans round_39_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_39_18 = s_39_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_39_18).trans round_39_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 10 = s_39_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_39_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_39_19 = s_39_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_39_19).trans round_39_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_39_20 = s_39_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_39_20).trans round_39_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) 11 = s_39_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_39_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_39_21 = s_39_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_39_21).trans round_39_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_39_22 = s_39_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_39_22).trans round_39_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell3919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell3919.canon3
  · exact PV_RunJoin_ValidatorCell3919.canon5
  · exact PV_RunJoin_ValidatorCell3919.canon7
  · exact PV_RunJoin_ValidatorCell3919.canon9
  · exact PV_RunJoin_ValidatorCell3919.canon11
  · exact PV_RunJoin_ValidatorCell3919.canon13
  · exact PV_RunJoin_ValidatorCell3919.canon15
  · exact PV_RunJoin_ValidatorCell3919.canon17
  · exact PV_RunJoin_ValidatorCell3919.canon19
  · exact PV_RunJoin_ValidatorCell3919.canon21
  · exact PV_RunJoin_ValidatorCell3919.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3919.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell3919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell3919.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell3919.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell3919.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell3919.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell3919.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell3919.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell3919.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell3919.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell3919.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell3919.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell3919.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell3919.certificate.pre PV_RunJoin_BankCell3919.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell3919.certificate.pre PV_RunJoin_BankCell3919.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell3919.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell3920

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell4020
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell4019.certificate.pre) i +
    (liftA PV_RunJoin_BankCell4019.certificate.absorption) i else (liftA PV_RunJoin_BankCell4019.certificate.pre) i) = s_40_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 1 = s_40_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell4019.certificate.pre) (liftA PV_RunJoin_BankCell4019.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_40_1,round_40_2]
  exact round_40_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 2 = s_40_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_40_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_40_3 = s_40_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_40_3).trans round_40_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_40_4 = s_40_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_40_4).trans round_40_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 3 = s_40_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_40_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_40_5 = s_40_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_40_5).trans round_40_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_40_6 = s_40_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_40_6).trans round_40_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 4 = s_40_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_40_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_40_7 = s_40_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_40_7).trans round_40_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_40_8 = s_40_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_40_8).trans round_40_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 5 = s_40_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_40_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_40_9 = s_40_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_40_9).trans round_40_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_40_10 = s_40_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_40_10).trans round_40_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 6 = s_40_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_40_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_40_11 = s_40_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_40_11).trans round_40_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_40_12 = s_40_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_40_12).trans round_40_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 7 = s_40_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_40_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_40_13 = s_40_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_40_13).trans round_40_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_40_14 = s_40_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_40_14).trans round_40_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 8 = s_40_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_40_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_40_15 = s_40_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_40_15).trans round_40_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_40_16 = s_40_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_40_16).trans round_40_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 9 = s_40_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_40_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_40_17 = s_40_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_40_17).trans round_40_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_40_18 = s_40_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_40_18).trans round_40_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 10 = s_40_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_40_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_40_19 = s_40_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_40_19).trans round_40_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_40_20 = s_40_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_40_20).trans round_40_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) 11 = s_40_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_40_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_40_21 = s_40_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_40_21).trans round_40_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_40_22 = s_40_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_40_22).trans round_40_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell4019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell4019.canon3
  · exact PV_RunJoin_ValidatorCell4019.canon5
  · exact PV_RunJoin_ValidatorCell4019.canon7
  · exact PV_RunJoin_ValidatorCell4019.canon9
  · exact PV_RunJoin_ValidatorCell4019.canon11
  · exact PV_RunJoin_ValidatorCell4019.canon13
  · exact PV_RunJoin_ValidatorCell4019.canon15
  · exact PV_RunJoin_ValidatorCell4019.canon17
  · exact PV_RunJoin_ValidatorCell4019.canon19
  · exact PV_RunJoin_ValidatorCell4019.canon21
  · exact PV_RunJoin_ValidatorCell4019.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4019.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell4019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell4019.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell4019.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell4019.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell4019.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell4019.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell4019.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell4019.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell4019.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell4019.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell4019.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell4019.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell4019.certificate.pre PV_RunJoin_BankCell4019.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell4019.certificate.pre PV_RunJoin_BankCell4019.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell4019.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell4020

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell4120
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell4119.certificate.pre) i +
    (liftA PV_RunJoin_BankCell4119.certificate.absorption) i else (liftA PV_RunJoin_BankCell4119.certificate.pre) i) = s_41_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 1 = s_41_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell4119.certificate.pre) (liftA PV_RunJoin_BankCell4119.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_41_1,round_41_2]
  exact round_41_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 2 = s_41_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_41_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_41_3 = s_41_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_41_3).trans round_41_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_41_4 = s_41_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_41_4).trans round_41_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 3 = s_41_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_41_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_41_5 = s_41_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_41_5).trans round_41_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_41_6 = s_41_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_41_6).trans round_41_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 4 = s_41_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_41_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_41_7 = s_41_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_41_7).trans round_41_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_41_8 = s_41_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_41_8).trans round_41_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 5 = s_41_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_41_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_41_9 = s_41_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_41_9).trans round_41_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_41_10 = s_41_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_41_10).trans round_41_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 6 = s_41_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_41_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_41_11 = s_41_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_41_11).trans round_41_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_41_12 = s_41_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_41_12).trans round_41_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 7 = s_41_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_41_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_41_13 = s_41_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_41_13).trans round_41_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_41_14 = s_41_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_41_14).trans round_41_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 8 = s_41_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_41_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_41_15 = s_41_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_41_15).trans round_41_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_41_16 = s_41_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_41_16).trans round_41_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 9 = s_41_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_41_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_41_17 = s_41_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_41_17).trans round_41_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_41_18 = s_41_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_41_18).trans round_41_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 10 = s_41_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_41_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_41_19 = s_41_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_41_19).trans round_41_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_41_20 = s_41_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_41_20).trans round_41_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) 11 = s_41_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_41_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_41_21 = s_41_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_41_21).trans round_41_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_41_22 = s_41_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_41_22).trans round_41_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell4119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell4119.canon3
  · exact PV_RunJoin_ValidatorCell4119.canon5
  · exact PV_RunJoin_ValidatorCell4119.canon7
  · exact PV_RunJoin_ValidatorCell4119.canon9
  · exact PV_RunJoin_ValidatorCell4119.canon11
  · exact PV_RunJoin_ValidatorCell4119.canon13
  · exact PV_RunJoin_ValidatorCell4119.canon15
  · exact PV_RunJoin_ValidatorCell4119.canon17
  · exact PV_RunJoin_ValidatorCell4119.canon19
  · exact PV_RunJoin_ValidatorCell4119.canon21
  · exact PV_RunJoin_ValidatorCell4119.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4119.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell4119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell4119.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell4119.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell4119.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell4119.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell4119.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell4119.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell4119.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell4119.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell4119.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell4119.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell4119.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell4119.certificate.pre PV_RunJoin_BankCell4119.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell4119.certificate.pre PV_RunJoin_BankCell4119.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell4119.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell4120

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell4220
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell4219.certificate.pre) i +
    (liftA PV_RunJoin_BankCell4219.certificate.absorption) i else (liftA PV_RunJoin_BankCell4219.certificate.pre) i) = s_42_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 1 = s_42_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell4219.certificate.pre) (liftA PV_RunJoin_BankCell4219.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_42_1,round_42_2]
  exact round_42_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 2 = s_42_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_42_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_42_3 = s_42_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_42_3).trans round_42_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_42_4 = s_42_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_42_4).trans round_42_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 3 = s_42_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_42_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_42_5 = s_42_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_42_5).trans round_42_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_42_6 = s_42_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_42_6).trans round_42_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 4 = s_42_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_42_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_42_7 = s_42_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_42_7).trans round_42_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_42_8 = s_42_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_42_8).trans round_42_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 5 = s_42_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_42_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_42_9 = s_42_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_42_9).trans round_42_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_42_10 = s_42_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_42_10).trans round_42_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 6 = s_42_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_42_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_42_11 = s_42_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_42_11).trans round_42_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_42_12 = s_42_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_42_12).trans round_42_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 7 = s_42_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_42_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_42_13 = s_42_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_42_13).trans round_42_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_42_14 = s_42_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_42_14).trans round_42_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 8 = s_42_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_42_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_42_15 = s_42_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_42_15).trans round_42_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_42_16 = s_42_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_42_16).trans round_42_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 9 = s_42_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_42_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_42_17 = s_42_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_42_17).trans round_42_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_42_18 = s_42_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_42_18).trans round_42_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 10 = s_42_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_42_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_42_19 = s_42_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_42_19).trans round_42_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_42_20 = s_42_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_42_20).trans round_42_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) 11 = s_42_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_42_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_42_21 = s_42_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_42_21).trans round_42_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_42_22 = s_42_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_42_22).trans round_42_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell4219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell4219.canon3
  · exact PV_RunJoin_ValidatorCell4219.canon5
  · exact PV_RunJoin_ValidatorCell4219.canon7
  · exact PV_RunJoin_ValidatorCell4219.canon9
  · exact PV_RunJoin_ValidatorCell4219.canon11
  · exact PV_RunJoin_ValidatorCell4219.canon13
  · exact PV_RunJoin_ValidatorCell4219.canon15
  · exact PV_RunJoin_ValidatorCell4219.canon17
  · exact PV_RunJoin_ValidatorCell4219.canon19
  · exact PV_RunJoin_ValidatorCell4219.canon21
  · exact PV_RunJoin_ValidatorCell4219.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4219.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell4219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell4219.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell4219.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell4219.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell4219.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell4219.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell4219.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell4219.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell4219.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell4219.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell4219.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell4219.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell4219.certificate.pre PV_RunJoin_BankCell4219.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell4219.certificate.pre PV_RunJoin_BankCell4219.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell4219.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell4220

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell4320
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell4319.certificate.pre) i +
    (liftA PV_RunJoin_BankCell4319.certificate.absorption) i else (liftA PV_RunJoin_BankCell4319.certificate.pre) i) = s_43_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 1 = s_43_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell4319.certificate.pre) (liftA PV_RunJoin_BankCell4319.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_43_1,round_43_2]
  exact round_43_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 2 = s_43_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_43_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_43_3 = s_43_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_43_3).trans round_43_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_43_4 = s_43_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_43_4).trans round_43_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 3 = s_43_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_43_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_43_5 = s_43_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_43_5).trans round_43_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_43_6 = s_43_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_43_6).trans round_43_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 4 = s_43_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_43_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_43_7 = s_43_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_43_7).trans round_43_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_43_8 = s_43_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_43_8).trans round_43_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 5 = s_43_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_43_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_43_9 = s_43_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_43_9).trans round_43_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_43_10 = s_43_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_43_10).trans round_43_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 6 = s_43_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_43_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_43_11 = s_43_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_43_11).trans round_43_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_43_12 = s_43_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_43_12).trans round_43_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 7 = s_43_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_43_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_43_13 = s_43_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_43_13).trans round_43_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_43_14 = s_43_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_43_14).trans round_43_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 8 = s_43_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_43_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_43_15 = s_43_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_43_15).trans round_43_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_43_16 = s_43_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_43_16).trans round_43_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 9 = s_43_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_43_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_43_17 = s_43_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_43_17).trans round_43_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_43_18 = s_43_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_43_18).trans round_43_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 10 = s_43_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_43_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_43_19 = s_43_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_43_19).trans round_43_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_43_20 = s_43_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_43_20).trans round_43_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) 11 = s_43_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_43_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_43_21 = s_43_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_43_21).trans round_43_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_43_22 = s_43_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_43_22).trans round_43_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell4319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell4319.canon3
  · exact PV_RunJoin_ValidatorCell4319.canon5
  · exact PV_RunJoin_ValidatorCell4319.canon7
  · exact PV_RunJoin_ValidatorCell4319.canon9
  · exact PV_RunJoin_ValidatorCell4319.canon11
  · exact PV_RunJoin_ValidatorCell4319.canon13
  · exact PV_RunJoin_ValidatorCell4319.canon15
  · exact PV_RunJoin_ValidatorCell4319.canon17
  · exact PV_RunJoin_ValidatorCell4319.canon19
  · exact PV_RunJoin_ValidatorCell4319.canon21
  · exact PV_RunJoin_ValidatorCell4319.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4319.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell4319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell4319.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell4319.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell4319.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell4319.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell4319.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell4319.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell4319.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell4319.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell4319.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell4319.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell4319.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell4319.certificate.pre PV_RunJoin_BankCell4319.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell4319.certificate.pre PV_RunJoin_BankCell4319.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell4319.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell4320

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell4420
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell4419.certificate.pre) i +
    (liftA PV_RunJoin_BankCell4419.certificate.absorption) i else (liftA PV_RunJoin_BankCell4419.certificate.pre) i) = s_44_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 1 = s_44_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell4419.certificate.pre) (liftA PV_RunJoin_BankCell4419.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_44_1,round_44_2]
  exact round_44_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 2 = s_44_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_44_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_44_3 = s_44_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_44_3).trans round_44_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_44_4 = s_44_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_44_4).trans round_44_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 3 = s_44_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_44_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_44_5 = s_44_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_44_5).trans round_44_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_44_6 = s_44_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_44_6).trans round_44_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 4 = s_44_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_44_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_44_7 = s_44_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_44_7).trans round_44_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_44_8 = s_44_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_44_8).trans round_44_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 5 = s_44_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_44_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_44_9 = s_44_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_44_9).trans round_44_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_44_10 = s_44_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_44_10).trans round_44_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 6 = s_44_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_44_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_44_11 = s_44_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_44_11).trans round_44_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_44_12 = s_44_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_44_12).trans round_44_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 7 = s_44_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_44_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_44_13 = s_44_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_44_13).trans round_44_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_44_14 = s_44_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_44_14).trans round_44_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 8 = s_44_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_44_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_44_15 = s_44_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_44_15).trans round_44_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_44_16 = s_44_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_44_16).trans round_44_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 9 = s_44_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_44_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_44_17 = s_44_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_44_17).trans round_44_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_44_18 = s_44_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_44_18).trans round_44_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 10 = s_44_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_44_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_44_19 = s_44_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_44_19).trans round_44_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_44_20 = s_44_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_44_20).trans round_44_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) 11 = s_44_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_44_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_44_21 = s_44_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_44_21).trans round_44_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_44_22 = s_44_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_44_22).trans round_44_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell4419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell4419.canon3
  · exact PV_RunJoin_ValidatorCell4419.canon5
  · exact PV_RunJoin_ValidatorCell4419.canon7
  · exact PV_RunJoin_ValidatorCell4419.canon9
  · exact PV_RunJoin_ValidatorCell4419.canon11
  · exact PV_RunJoin_ValidatorCell4419.canon13
  · exact PV_RunJoin_ValidatorCell4419.canon15
  · exact PV_RunJoin_ValidatorCell4419.canon17
  · exact PV_RunJoin_ValidatorCell4419.canon19
  · exact PV_RunJoin_ValidatorCell4419.canon21
  · exact PV_RunJoin_ValidatorCell4419.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell4419.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell4419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell4419.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell4419.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell4419.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell4419.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell4419.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell4419.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell4419.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell4419.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell4419.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell4419.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell4419.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell4419.certificate.pre PV_RunJoin_BankCell4419.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell4419.certificate.pre PV_RunJoin_BankCell4419.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell4419.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell4420
