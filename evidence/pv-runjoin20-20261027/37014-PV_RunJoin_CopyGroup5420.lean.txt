import R1Z.PV_RunJoin_CopyCertificate20
import R1Z.PV_RunJoin_BankCells5419
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell5420
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell5419.certificate.pre) i +
    (liftA PV_RunJoin_BankCell5419.certificate.absorption) i else (liftA PV_RunJoin_BankCell5419.certificate.pre) i) = s_54_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 1 = s_54_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell5419.certificate.pre) (liftA PV_RunJoin_BankCell5419.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_54_1,round_54_2]
  exact round_54_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 2 = s_54_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_54_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_54_3 = s_54_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_54_3).trans round_54_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_54_4 = s_54_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_54_4).trans round_54_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 3 = s_54_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_54_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_54_5 = s_54_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_54_5).trans round_54_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_54_6 = s_54_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_54_6).trans round_54_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 4 = s_54_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_54_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_54_7 = s_54_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_54_7).trans round_54_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_54_8 = s_54_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_54_8).trans round_54_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 5 = s_54_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_54_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_54_9 = s_54_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_54_9).trans round_54_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_54_10 = s_54_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_54_10).trans round_54_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 6 = s_54_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_54_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_54_11 = s_54_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_54_11).trans round_54_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_54_12 = s_54_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_54_12).trans round_54_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 7 = s_54_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_54_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_54_13 = s_54_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_54_13).trans round_54_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_54_14 = s_54_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_54_14).trans round_54_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 8 = s_54_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_54_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_54_15 = s_54_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_54_15).trans round_54_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_54_16 = s_54_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_54_16).trans round_54_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 9 = s_54_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_54_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_54_17 = s_54_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_54_17).trans round_54_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_54_18 = s_54_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_54_18).trans round_54_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 10 = s_54_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_54_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_54_19 = s_54_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_54_19).trans round_54_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_54_20 = s_54_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_54_20).trans round_54_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) 11 = s_54_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_54_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_54_21 = s_54_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_54_21).trans round_54_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_54_22 = s_54_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_54_22).trans round_54_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell5419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell5419.canon3
  · exact PV_RunJoin_ValidatorCell5419.canon5
  · exact PV_RunJoin_ValidatorCell5419.canon7
  · exact PV_RunJoin_ValidatorCell5419.canon9
  · exact PV_RunJoin_ValidatorCell5419.canon11
  · exact PV_RunJoin_ValidatorCell5419.canon13
  · exact PV_RunJoin_ValidatorCell5419.canon15
  · exact PV_RunJoin_ValidatorCell5419.canon17
  · exact PV_RunJoin_ValidatorCell5419.canon19
  · exact PV_RunJoin_ValidatorCell5419.canon21
  · exact PV_RunJoin_ValidatorCell5419.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5419.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell5419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell5419.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell5419.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell5419.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell5419.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell5419.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell5419.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell5419.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell5419.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell5419.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell5419.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell5419.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell5419.certificate.pre PV_RunJoin_BankCell5419.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell5419.certificate.pre PV_RunJoin_BankCell5419.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell5419.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell5420

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell5520
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell5519.certificate.pre) i +
    (liftA PV_RunJoin_BankCell5519.certificate.absorption) i else (liftA PV_RunJoin_BankCell5519.certificate.pre) i) = s_55_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 1 = s_55_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell5519.certificate.pre) (liftA PV_RunJoin_BankCell5519.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_55_1,round_55_2]
  exact round_55_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 2 = s_55_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_55_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_55_3 = s_55_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_55_3).trans round_55_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_55_4 = s_55_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_55_4).trans round_55_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 3 = s_55_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_55_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_55_5 = s_55_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_55_5).trans round_55_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_55_6 = s_55_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_55_6).trans round_55_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 4 = s_55_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_55_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_55_7 = s_55_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_55_7).trans round_55_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_55_8 = s_55_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_55_8).trans round_55_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 5 = s_55_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_55_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_55_9 = s_55_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_55_9).trans round_55_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_55_10 = s_55_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_55_10).trans round_55_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 6 = s_55_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_55_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_55_11 = s_55_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_55_11).trans round_55_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_55_12 = s_55_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_55_12).trans round_55_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 7 = s_55_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_55_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_55_13 = s_55_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_55_13).trans round_55_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_55_14 = s_55_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_55_14).trans round_55_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 8 = s_55_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_55_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_55_15 = s_55_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_55_15).trans round_55_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_55_16 = s_55_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_55_16).trans round_55_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 9 = s_55_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_55_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_55_17 = s_55_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_55_17).trans round_55_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_55_18 = s_55_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_55_18).trans round_55_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 10 = s_55_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_55_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_55_19 = s_55_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_55_19).trans round_55_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_55_20 = s_55_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_55_20).trans round_55_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) 11 = s_55_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_55_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_55_21 = s_55_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_55_21).trans round_55_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_55_22 = s_55_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_55_22).trans round_55_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell5519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell5519.canon3
  · exact PV_RunJoin_ValidatorCell5519.canon5
  · exact PV_RunJoin_ValidatorCell5519.canon7
  · exact PV_RunJoin_ValidatorCell5519.canon9
  · exact PV_RunJoin_ValidatorCell5519.canon11
  · exact PV_RunJoin_ValidatorCell5519.canon13
  · exact PV_RunJoin_ValidatorCell5519.canon15
  · exact PV_RunJoin_ValidatorCell5519.canon17
  · exact PV_RunJoin_ValidatorCell5519.canon19
  · exact PV_RunJoin_ValidatorCell5519.canon21
  · exact PV_RunJoin_ValidatorCell5519.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5519.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell5519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell5519.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell5519.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell5519.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell5519.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell5519.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell5519.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell5519.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell5519.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell5519.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell5519.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell5519.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell5519.certificate.pre PV_RunJoin_BankCell5519.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell5519.certificate.pre PV_RunJoin_BankCell5519.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell5519.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell5520

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell5620
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell5619.certificate.pre) i +
    (liftA PV_RunJoin_BankCell5619.certificate.absorption) i else (liftA PV_RunJoin_BankCell5619.certificate.pre) i) = s_56_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 1 = s_56_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell5619.certificate.pre) (liftA PV_RunJoin_BankCell5619.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_56_1,round_56_2]
  exact round_56_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 2 = s_56_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_56_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_56_3 = s_56_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_56_3).trans round_56_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_56_4 = s_56_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_56_4).trans round_56_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 3 = s_56_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_56_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_56_5 = s_56_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_56_5).trans round_56_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_56_6 = s_56_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_56_6).trans round_56_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 4 = s_56_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_56_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_56_7 = s_56_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_56_7).trans round_56_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_56_8 = s_56_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_56_8).trans round_56_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 5 = s_56_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_56_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_56_9 = s_56_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_56_9).trans round_56_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_56_10 = s_56_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_56_10).trans round_56_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 6 = s_56_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_56_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_56_11 = s_56_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_56_11).trans round_56_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_56_12 = s_56_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_56_12).trans round_56_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 7 = s_56_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_56_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_56_13 = s_56_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_56_13).trans round_56_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_56_14 = s_56_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_56_14).trans round_56_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 8 = s_56_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_56_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_56_15 = s_56_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_56_15).trans round_56_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_56_16 = s_56_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_56_16).trans round_56_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 9 = s_56_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_56_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_56_17 = s_56_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_56_17).trans round_56_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_56_18 = s_56_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_56_18).trans round_56_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 10 = s_56_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_56_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_56_19 = s_56_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_56_19).trans round_56_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_56_20 = s_56_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_56_20).trans round_56_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) 11 = s_56_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_56_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_56_21 = s_56_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_56_21).trans round_56_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_56_22 = s_56_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_56_22).trans round_56_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell5619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell5619.canon3
  · exact PV_RunJoin_ValidatorCell5619.canon5
  · exact PV_RunJoin_ValidatorCell5619.canon7
  · exact PV_RunJoin_ValidatorCell5619.canon9
  · exact PV_RunJoin_ValidatorCell5619.canon11
  · exact PV_RunJoin_ValidatorCell5619.canon13
  · exact PV_RunJoin_ValidatorCell5619.canon15
  · exact PV_RunJoin_ValidatorCell5619.canon17
  · exact PV_RunJoin_ValidatorCell5619.canon19
  · exact PV_RunJoin_ValidatorCell5619.canon21
  · exact PV_RunJoin_ValidatorCell5619.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5619.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell5619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell5619.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell5619.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell5619.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell5619.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell5619.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell5619.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell5619.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell5619.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell5619.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell5619.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell5619.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell5619.certificate.pre PV_RunJoin_BankCell5619.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell5619.certificate.pre PV_RunJoin_BankCell5619.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell5619.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell5620

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell5720
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell5719.certificate.pre) i +
    (liftA PV_RunJoin_BankCell5719.certificate.absorption) i else (liftA PV_RunJoin_BankCell5719.certificate.pre) i) = s_57_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 1 = s_57_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell5719.certificate.pre) (liftA PV_RunJoin_BankCell5719.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_57_1,round_57_2]
  exact round_57_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 2 = s_57_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_57_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_57_3 = s_57_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_57_3).trans round_57_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_57_4 = s_57_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_57_4).trans round_57_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 3 = s_57_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_57_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_57_5 = s_57_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_57_5).trans round_57_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_57_6 = s_57_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_57_6).trans round_57_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 4 = s_57_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_57_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_57_7 = s_57_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_57_7).trans round_57_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_57_8 = s_57_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_57_8).trans round_57_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 5 = s_57_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_57_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_57_9 = s_57_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_57_9).trans round_57_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_57_10 = s_57_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_57_10).trans round_57_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 6 = s_57_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_57_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_57_11 = s_57_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_57_11).trans round_57_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_57_12 = s_57_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_57_12).trans round_57_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 7 = s_57_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_57_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_57_13 = s_57_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_57_13).trans round_57_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_57_14 = s_57_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_57_14).trans round_57_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 8 = s_57_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_57_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_57_15 = s_57_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_57_15).trans round_57_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_57_16 = s_57_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_57_16).trans round_57_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 9 = s_57_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_57_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_57_17 = s_57_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_57_17).trans round_57_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_57_18 = s_57_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_57_18).trans round_57_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 10 = s_57_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_57_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_57_19 = s_57_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_57_19).trans round_57_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_57_20 = s_57_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_57_20).trans round_57_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) 11 = s_57_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_57_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_57_21 = s_57_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_57_21).trans round_57_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_57_22 = s_57_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_57_22).trans round_57_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell5719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell5719.canon3
  · exact PV_RunJoin_ValidatorCell5719.canon5
  · exact PV_RunJoin_ValidatorCell5719.canon7
  · exact PV_RunJoin_ValidatorCell5719.canon9
  · exact PV_RunJoin_ValidatorCell5719.canon11
  · exact PV_RunJoin_ValidatorCell5719.canon13
  · exact PV_RunJoin_ValidatorCell5719.canon15
  · exact PV_RunJoin_ValidatorCell5719.canon17
  · exact PV_RunJoin_ValidatorCell5719.canon19
  · exact PV_RunJoin_ValidatorCell5719.canon21
  · exact PV_RunJoin_ValidatorCell5719.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5719.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell5719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell5719.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell5719.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell5719.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell5719.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell5719.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell5719.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell5719.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell5719.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell5719.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell5719.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell5719.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell5719.certificate.pre PV_RunJoin_BankCell5719.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell5719.certificate.pre PV_RunJoin_BankCell5719.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell5719.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell5720

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell5820
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell5819.certificate.pre) i +
    (liftA PV_RunJoin_BankCell5819.certificate.absorption) i else (liftA PV_RunJoin_BankCell5819.certificate.pre) i) = s_58_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 1 = s_58_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell5819.certificate.pre) (liftA PV_RunJoin_BankCell5819.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_58_1,round_58_2]
  exact round_58_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 2 = s_58_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_58_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_58_3 = s_58_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_58_3).trans round_58_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_58_4 = s_58_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_58_4).trans round_58_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 3 = s_58_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_58_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_58_5 = s_58_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_58_5).trans round_58_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_58_6 = s_58_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_58_6).trans round_58_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 4 = s_58_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_58_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_58_7 = s_58_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_58_7).trans round_58_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_58_8 = s_58_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_58_8).trans round_58_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 5 = s_58_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_58_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_58_9 = s_58_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_58_9).trans round_58_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_58_10 = s_58_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_58_10).trans round_58_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 6 = s_58_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_58_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_58_11 = s_58_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_58_11).trans round_58_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_58_12 = s_58_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_58_12).trans round_58_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 7 = s_58_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_58_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_58_13 = s_58_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_58_13).trans round_58_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_58_14 = s_58_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_58_14).trans round_58_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 8 = s_58_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_58_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_58_15 = s_58_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_58_15).trans round_58_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_58_16 = s_58_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_58_16).trans round_58_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 9 = s_58_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_58_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_58_17 = s_58_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_58_17).trans round_58_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_58_18 = s_58_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_58_18).trans round_58_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 10 = s_58_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_58_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_58_19 = s_58_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_58_19).trans round_58_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_58_20 = s_58_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_58_20).trans round_58_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) 11 = s_58_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_58_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_58_21 = s_58_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_58_21).trans round_58_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_58_22 = s_58_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_58_22).trans round_58_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell5819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell5819.canon3
  · exact PV_RunJoin_ValidatorCell5819.canon5
  · exact PV_RunJoin_ValidatorCell5819.canon7
  · exact PV_RunJoin_ValidatorCell5819.canon9
  · exact PV_RunJoin_ValidatorCell5819.canon11
  · exact PV_RunJoin_ValidatorCell5819.canon13
  · exact PV_RunJoin_ValidatorCell5819.canon15
  · exact PV_RunJoin_ValidatorCell5819.canon17
  · exact PV_RunJoin_ValidatorCell5819.canon19
  · exact PV_RunJoin_ValidatorCell5819.canon21
  · exact PV_RunJoin_ValidatorCell5819.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5819.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell5819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell5819.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell5819.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell5819.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell5819.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell5819.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell5819.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell5819.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell5819.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell5819.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell5819.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell5819.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell5819.certificate.pre PV_RunJoin_BankCell5819.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell5819.certificate.pre PV_RunJoin_BankCell5819.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell5819.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell5820

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell5920
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell5919.certificate.pre) i +
    (liftA PV_RunJoin_BankCell5919.certificate.absorption) i else (liftA PV_RunJoin_BankCell5919.certificate.pre) i) = s_59_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 1 = s_59_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell5919.certificate.pre) (liftA PV_RunJoin_BankCell5919.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_59_1,round_59_2]
  exact round_59_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 2 = s_59_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_59_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_59_3 = s_59_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_59_3).trans round_59_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_59_4 = s_59_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_59_4).trans round_59_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 3 = s_59_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_59_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_59_5 = s_59_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_59_5).trans round_59_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_59_6 = s_59_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_59_6).trans round_59_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 4 = s_59_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_59_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_59_7 = s_59_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_59_7).trans round_59_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_59_8 = s_59_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_59_8).trans round_59_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 5 = s_59_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_59_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_59_9 = s_59_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_59_9).trans round_59_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_59_10 = s_59_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_59_10).trans round_59_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 6 = s_59_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_59_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_59_11 = s_59_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_59_11).trans round_59_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_59_12 = s_59_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_59_12).trans round_59_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 7 = s_59_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_59_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_59_13 = s_59_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_59_13).trans round_59_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_59_14 = s_59_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_59_14).trans round_59_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 8 = s_59_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_59_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_59_15 = s_59_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_59_15).trans round_59_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_59_16 = s_59_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_59_16).trans round_59_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 9 = s_59_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_59_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_59_17 = s_59_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_59_17).trans round_59_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_59_18 = s_59_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_59_18).trans round_59_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 10 = s_59_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_59_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_59_19 = s_59_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_59_19).trans round_59_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_59_20 = s_59_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_59_20).trans round_59_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) 11 = s_59_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_59_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_59_21 = s_59_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_59_21).trans round_59_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_59_22 = s_59_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_59_22).trans round_59_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell5919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell5919.canon3
  · exact PV_RunJoin_ValidatorCell5919.canon5
  · exact PV_RunJoin_ValidatorCell5919.canon7
  · exact PV_RunJoin_ValidatorCell5919.canon9
  · exact PV_RunJoin_ValidatorCell5919.canon11
  · exact PV_RunJoin_ValidatorCell5919.canon13
  · exact PV_RunJoin_ValidatorCell5919.canon15
  · exact PV_RunJoin_ValidatorCell5919.canon17
  · exact PV_RunJoin_ValidatorCell5919.canon19
  · exact PV_RunJoin_ValidatorCell5919.canon21
  · exact PV_RunJoin_ValidatorCell5919.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell5919.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell5919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell5919.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell5919.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell5919.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell5919.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell5919.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell5919.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell5919.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell5919.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell5919.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell5919.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell5919.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell5919.certificate.pre PV_RunJoin_BankCell5919.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell5919.certificate.pre PV_RunJoin_BankCell5919.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell5919.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell5920

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell6020
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell6019.certificate.pre) i +
    (liftA PV_RunJoin_BankCell6019.certificate.absorption) i else (liftA PV_RunJoin_BankCell6019.certificate.pre) i) = s_60_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 1 = s_60_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell6019.certificate.pre) (liftA PV_RunJoin_BankCell6019.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_60_1,round_60_2]
  exact round_60_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 2 = s_60_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_60_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_60_3 = s_60_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_60_3).trans round_60_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_60_4 = s_60_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_60_4).trans round_60_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 3 = s_60_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_60_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_60_5 = s_60_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_60_5).trans round_60_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_60_6 = s_60_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_60_6).trans round_60_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 4 = s_60_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_60_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_60_7 = s_60_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_60_7).trans round_60_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_60_8 = s_60_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_60_8).trans round_60_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 5 = s_60_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_60_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_60_9 = s_60_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_60_9).trans round_60_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_60_10 = s_60_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_60_10).trans round_60_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 6 = s_60_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_60_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_60_11 = s_60_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_60_11).trans round_60_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_60_12 = s_60_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_60_12).trans round_60_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 7 = s_60_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_60_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_60_13 = s_60_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_60_13).trans round_60_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_60_14 = s_60_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_60_14).trans round_60_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 8 = s_60_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_60_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_60_15 = s_60_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_60_15).trans round_60_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_60_16 = s_60_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_60_16).trans round_60_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 9 = s_60_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_60_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_60_17 = s_60_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_60_17).trans round_60_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_60_18 = s_60_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_60_18).trans round_60_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 10 = s_60_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_60_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_60_19 = s_60_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_60_19).trans round_60_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_60_20 = s_60_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_60_20).trans round_60_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) 11 = s_60_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_60_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_60_21 = s_60_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_60_21).trans round_60_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_60_22 = s_60_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_60_22).trans round_60_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell6019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell6019.canon3
  · exact PV_RunJoin_ValidatorCell6019.canon5
  · exact PV_RunJoin_ValidatorCell6019.canon7
  · exact PV_RunJoin_ValidatorCell6019.canon9
  · exact PV_RunJoin_ValidatorCell6019.canon11
  · exact PV_RunJoin_ValidatorCell6019.canon13
  · exact PV_RunJoin_ValidatorCell6019.canon15
  · exact PV_RunJoin_ValidatorCell6019.canon17
  · exact PV_RunJoin_ValidatorCell6019.canon19
  · exact PV_RunJoin_ValidatorCell6019.canon21
  · exact PV_RunJoin_ValidatorCell6019.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6019.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell6019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell6019.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell6019.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell6019.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell6019.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell6019.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell6019.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell6019.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell6019.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell6019.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell6019.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell6019.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell6019.certificate.pre PV_RunJoin_BankCell6019.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell6019.certificate.pre PV_RunJoin_BankCell6019.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell6019.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell6020

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell6120
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell6119.certificate.pre) i +
    (liftA PV_RunJoin_BankCell6119.certificate.absorption) i else (liftA PV_RunJoin_BankCell6119.certificate.pre) i) = s_61_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 1 = s_61_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell6119.certificate.pre) (liftA PV_RunJoin_BankCell6119.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_61_1,round_61_2]
  exact round_61_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 2 = s_61_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_61_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_61_3 = s_61_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_61_3).trans round_61_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_61_4 = s_61_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_61_4).trans round_61_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 3 = s_61_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_61_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_61_5 = s_61_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_61_5).trans round_61_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_61_6 = s_61_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_61_6).trans round_61_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 4 = s_61_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_61_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_61_7 = s_61_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_61_7).trans round_61_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_61_8 = s_61_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_61_8).trans round_61_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 5 = s_61_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_61_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_61_9 = s_61_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_61_9).trans round_61_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_61_10 = s_61_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_61_10).trans round_61_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 6 = s_61_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_61_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_61_11 = s_61_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_61_11).trans round_61_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_61_12 = s_61_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_61_12).trans round_61_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 7 = s_61_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_61_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_61_13 = s_61_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_61_13).trans round_61_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_61_14 = s_61_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_61_14).trans round_61_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 8 = s_61_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_61_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_61_15 = s_61_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_61_15).trans round_61_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_61_16 = s_61_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_61_16).trans round_61_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 9 = s_61_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_61_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_61_17 = s_61_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_61_17).trans round_61_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_61_18 = s_61_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_61_18).trans round_61_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 10 = s_61_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_61_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_61_19 = s_61_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_61_19).trans round_61_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_61_20 = s_61_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_61_20).trans round_61_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) 11 = s_61_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_61_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_61_21 = s_61_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_61_21).trans round_61_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_61_22 = s_61_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_61_22).trans round_61_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell6119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell6119.canon3
  · exact PV_RunJoin_ValidatorCell6119.canon5
  · exact PV_RunJoin_ValidatorCell6119.canon7
  · exact PV_RunJoin_ValidatorCell6119.canon9
  · exact PV_RunJoin_ValidatorCell6119.canon11
  · exact PV_RunJoin_ValidatorCell6119.canon13
  · exact PV_RunJoin_ValidatorCell6119.canon15
  · exact PV_RunJoin_ValidatorCell6119.canon17
  · exact PV_RunJoin_ValidatorCell6119.canon19
  · exact PV_RunJoin_ValidatorCell6119.canon21
  · exact PV_RunJoin_ValidatorCell6119.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6119.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell6119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell6119.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell6119.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell6119.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell6119.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell6119.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell6119.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell6119.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell6119.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell6119.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell6119.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell6119.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell6119.certificate.pre PV_RunJoin_BankCell6119.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell6119.certificate.pre PV_RunJoin_BankCell6119.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell6119.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell6120

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell6220
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell6219.certificate.pre) i +
    (liftA PV_RunJoin_BankCell6219.certificate.absorption) i else (liftA PV_RunJoin_BankCell6219.certificate.pre) i) = s_62_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 1 = s_62_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell6219.certificate.pre) (liftA PV_RunJoin_BankCell6219.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_62_1,round_62_2]
  exact round_62_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 2 = s_62_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_62_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_62_3 = s_62_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_62_3).trans round_62_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_62_4 = s_62_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_62_4).trans round_62_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 3 = s_62_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_62_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_62_5 = s_62_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_62_5).trans round_62_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_62_6 = s_62_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_62_6).trans round_62_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 4 = s_62_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_62_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_62_7 = s_62_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_62_7).trans round_62_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_62_8 = s_62_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_62_8).trans round_62_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 5 = s_62_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_62_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_62_9 = s_62_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_62_9).trans round_62_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_62_10 = s_62_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_62_10).trans round_62_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 6 = s_62_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_62_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_62_11 = s_62_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_62_11).trans round_62_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_62_12 = s_62_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_62_12).trans round_62_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 7 = s_62_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_62_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_62_13 = s_62_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_62_13).trans round_62_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_62_14 = s_62_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_62_14).trans round_62_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 8 = s_62_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_62_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_62_15 = s_62_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_62_15).trans round_62_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_62_16 = s_62_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_62_16).trans round_62_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 9 = s_62_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_62_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_62_17 = s_62_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_62_17).trans round_62_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_62_18 = s_62_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_62_18).trans round_62_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 10 = s_62_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_62_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_62_19 = s_62_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_62_19).trans round_62_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_62_20 = s_62_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_62_20).trans round_62_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) 11 = s_62_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_62_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_62_21 = s_62_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_62_21).trans round_62_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_62_22 = s_62_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_62_22).trans round_62_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell6219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell6219.canon3
  · exact PV_RunJoin_ValidatorCell6219.canon5
  · exact PV_RunJoin_ValidatorCell6219.canon7
  · exact PV_RunJoin_ValidatorCell6219.canon9
  · exact PV_RunJoin_ValidatorCell6219.canon11
  · exact PV_RunJoin_ValidatorCell6219.canon13
  · exact PV_RunJoin_ValidatorCell6219.canon15
  · exact PV_RunJoin_ValidatorCell6219.canon17
  · exact PV_RunJoin_ValidatorCell6219.canon19
  · exact PV_RunJoin_ValidatorCell6219.canon21
  · exact PV_RunJoin_ValidatorCell6219.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell6219.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell6219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell6219.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell6219.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell6219.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell6219.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell6219.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell6219.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell6219.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell6219.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell6219.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell6219.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell6219.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell6219.certificate.pre PV_RunJoin_BankCell6219.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell6219.certificate.pre PV_RunJoin_BankCell6219.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell6219.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell6220
