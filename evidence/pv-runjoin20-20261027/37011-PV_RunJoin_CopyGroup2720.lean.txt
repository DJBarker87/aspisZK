import R1Z.PV_RunJoin_CopyCertificate20
import R1Z.PV_RunJoin_BankCells2719
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell2720
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell2719.certificate.pre) i +
    (liftA PV_RunJoin_BankCell2719.certificate.absorption) i else (liftA PV_RunJoin_BankCell2719.certificate.pre) i) = s_27_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 1 = s_27_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell2719.certificate.pre) (liftA PV_RunJoin_BankCell2719.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_27_1,round_27_2]
  exact round_27_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 2 = s_27_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_27_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_27_3 = s_27_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_27_3).trans round_27_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_27_4 = s_27_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_27_4).trans round_27_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 3 = s_27_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_27_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_27_5 = s_27_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_27_5).trans round_27_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_27_6 = s_27_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_27_6).trans round_27_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 4 = s_27_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_27_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_27_7 = s_27_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_27_7).trans round_27_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_27_8 = s_27_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_27_8).trans round_27_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 5 = s_27_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_27_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_27_9 = s_27_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_27_9).trans round_27_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_27_10 = s_27_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_27_10).trans round_27_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 6 = s_27_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_27_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_27_11 = s_27_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_27_11).trans round_27_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_27_12 = s_27_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_27_12).trans round_27_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 7 = s_27_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_27_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_27_13 = s_27_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_27_13).trans round_27_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_27_14 = s_27_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_27_14).trans round_27_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 8 = s_27_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_27_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_27_15 = s_27_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_27_15).trans round_27_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_27_16 = s_27_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_27_16).trans round_27_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 9 = s_27_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_27_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_27_17 = s_27_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_27_17).trans round_27_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_27_18 = s_27_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_27_18).trans round_27_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 10 = s_27_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_27_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_27_19 = s_27_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_27_19).trans round_27_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_27_20 = s_27_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_27_20).trans round_27_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) 11 = s_27_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_27_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_27_21 = s_27_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_27_21).trans round_27_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_27_22 = s_27_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_27_22).trans round_27_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell2719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell2719.canon3
  · exact PV_RunJoin_ValidatorCell2719.canon5
  · exact PV_RunJoin_ValidatorCell2719.canon7
  · exact PV_RunJoin_ValidatorCell2719.canon9
  · exact PV_RunJoin_ValidatorCell2719.canon11
  · exact PV_RunJoin_ValidatorCell2719.canon13
  · exact PV_RunJoin_ValidatorCell2719.canon15
  · exact PV_RunJoin_ValidatorCell2719.canon17
  · exact PV_RunJoin_ValidatorCell2719.canon19
  · exact PV_RunJoin_ValidatorCell2719.canon21
  · exact PV_RunJoin_ValidatorCell2719.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2719.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell2719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell2719.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell2719.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell2719.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell2719.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell2719.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell2719.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell2719.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell2719.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell2719.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell2719.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell2719.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell2719.certificate.pre PV_RunJoin_BankCell2719.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell2719.certificate.pre PV_RunJoin_BankCell2719.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell2719.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell2720

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell2820
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell2819.certificate.pre) i +
    (liftA PV_RunJoin_BankCell2819.certificate.absorption) i else (liftA PV_RunJoin_BankCell2819.certificate.pre) i) = s_28_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 1 = s_28_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell2819.certificate.pre) (liftA PV_RunJoin_BankCell2819.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_28_1,round_28_2]
  exact round_28_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 2 = s_28_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_28_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_28_3 = s_28_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_28_3).trans round_28_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_28_4 = s_28_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_28_4).trans round_28_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 3 = s_28_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_28_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_28_5 = s_28_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_28_5).trans round_28_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_28_6 = s_28_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_28_6).trans round_28_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 4 = s_28_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_28_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_28_7 = s_28_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_28_7).trans round_28_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_28_8 = s_28_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_28_8).trans round_28_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 5 = s_28_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_28_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_28_9 = s_28_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_28_9).trans round_28_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_28_10 = s_28_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_28_10).trans round_28_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 6 = s_28_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_28_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_28_11 = s_28_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_28_11).trans round_28_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_28_12 = s_28_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_28_12).trans round_28_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 7 = s_28_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_28_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_28_13 = s_28_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_28_13).trans round_28_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_28_14 = s_28_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_28_14).trans round_28_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 8 = s_28_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_28_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_28_15 = s_28_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_28_15).trans round_28_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_28_16 = s_28_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_28_16).trans round_28_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 9 = s_28_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_28_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_28_17 = s_28_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_28_17).trans round_28_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_28_18 = s_28_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_28_18).trans round_28_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 10 = s_28_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_28_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_28_19 = s_28_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_28_19).trans round_28_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_28_20 = s_28_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_28_20).trans round_28_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) 11 = s_28_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_28_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_28_21 = s_28_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_28_21).trans round_28_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_28_22 = s_28_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_28_22).trans round_28_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell2819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell2819.canon3
  · exact PV_RunJoin_ValidatorCell2819.canon5
  · exact PV_RunJoin_ValidatorCell2819.canon7
  · exact PV_RunJoin_ValidatorCell2819.canon9
  · exact PV_RunJoin_ValidatorCell2819.canon11
  · exact PV_RunJoin_ValidatorCell2819.canon13
  · exact PV_RunJoin_ValidatorCell2819.canon15
  · exact PV_RunJoin_ValidatorCell2819.canon17
  · exact PV_RunJoin_ValidatorCell2819.canon19
  · exact PV_RunJoin_ValidatorCell2819.canon21
  · exact PV_RunJoin_ValidatorCell2819.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2819.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell2819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell2819.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell2819.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell2819.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell2819.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell2819.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell2819.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell2819.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell2819.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell2819.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell2819.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell2819.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell2819.certificate.pre PV_RunJoin_BankCell2819.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell2819.certificate.pre PV_RunJoin_BankCell2819.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell2819.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell2820

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell2920
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell2919.certificate.pre) i +
    (liftA PV_RunJoin_BankCell2919.certificate.absorption) i else (liftA PV_RunJoin_BankCell2919.certificate.pre) i) = s_29_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 1 = s_29_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell2919.certificate.pre) (liftA PV_RunJoin_BankCell2919.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_29_1,round_29_2]
  exact round_29_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 2 = s_29_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_29_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_29_3 = s_29_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_29_3).trans round_29_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_29_4 = s_29_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_29_4).trans round_29_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 3 = s_29_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_29_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_29_5 = s_29_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_29_5).trans round_29_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_29_6 = s_29_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_29_6).trans round_29_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 4 = s_29_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_29_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_29_7 = s_29_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_29_7).trans round_29_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_29_8 = s_29_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_29_8).trans round_29_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 5 = s_29_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_29_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_29_9 = s_29_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_29_9).trans round_29_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_29_10 = s_29_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_29_10).trans round_29_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 6 = s_29_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_29_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_29_11 = s_29_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_29_11).trans round_29_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_29_12 = s_29_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_29_12).trans round_29_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 7 = s_29_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_29_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_29_13 = s_29_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_29_13).trans round_29_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_29_14 = s_29_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_29_14).trans round_29_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 8 = s_29_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_29_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_29_15 = s_29_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_29_15).trans round_29_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_29_16 = s_29_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_29_16).trans round_29_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 9 = s_29_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_29_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_29_17 = s_29_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_29_17).trans round_29_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_29_18 = s_29_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_29_18).trans round_29_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 10 = s_29_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_29_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_29_19 = s_29_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_29_19).trans round_29_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_29_20 = s_29_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_29_20).trans round_29_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) 11 = s_29_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_29_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_29_21 = s_29_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_29_21).trans round_29_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_29_22 = s_29_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_29_22).trans round_29_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell2919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell2919.canon3
  · exact PV_RunJoin_ValidatorCell2919.canon5
  · exact PV_RunJoin_ValidatorCell2919.canon7
  · exact PV_RunJoin_ValidatorCell2919.canon9
  · exact PV_RunJoin_ValidatorCell2919.canon11
  · exact PV_RunJoin_ValidatorCell2919.canon13
  · exact PV_RunJoin_ValidatorCell2919.canon15
  · exact PV_RunJoin_ValidatorCell2919.canon17
  · exact PV_RunJoin_ValidatorCell2919.canon19
  · exact PV_RunJoin_ValidatorCell2919.canon21
  · exact PV_RunJoin_ValidatorCell2919.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2919.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell2919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell2919.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell2919.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell2919.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell2919.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell2919.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell2919.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell2919.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell2919.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell2919.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell2919.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell2919.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell2919.certificate.pre PV_RunJoin_BankCell2919.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell2919.certificate.pre PV_RunJoin_BankCell2919.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell2919.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell2920

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell3020
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell3019.certificate.pre) i +
    (liftA PV_RunJoin_BankCell3019.certificate.absorption) i else (liftA PV_RunJoin_BankCell3019.certificate.pre) i) = s_30_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 1 = s_30_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell3019.certificate.pre) (liftA PV_RunJoin_BankCell3019.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_30_1,round_30_2]
  exact round_30_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 2 = s_30_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_30_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_30_3 = s_30_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_30_3).trans round_30_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_30_4 = s_30_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_30_4).trans round_30_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 3 = s_30_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_30_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_30_5 = s_30_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_30_5).trans round_30_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_30_6 = s_30_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_30_6).trans round_30_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 4 = s_30_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_30_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_30_7 = s_30_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_30_7).trans round_30_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_30_8 = s_30_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_30_8).trans round_30_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 5 = s_30_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_30_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_30_9 = s_30_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_30_9).trans round_30_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_30_10 = s_30_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_30_10).trans round_30_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 6 = s_30_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_30_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_30_11 = s_30_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_30_11).trans round_30_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_30_12 = s_30_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_30_12).trans round_30_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 7 = s_30_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_30_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_30_13 = s_30_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_30_13).trans round_30_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_30_14 = s_30_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_30_14).trans round_30_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 8 = s_30_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_30_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_30_15 = s_30_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_30_15).trans round_30_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_30_16 = s_30_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_30_16).trans round_30_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 9 = s_30_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_30_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_30_17 = s_30_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_30_17).trans round_30_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_30_18 = s_30_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_30_18).trans round_30_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 10 = s_30_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_30_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_30_19 = s_30_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_30_19).trans round_30_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_30_20 = s_30_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_30_20).trans round_30_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) 11 = s_30_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_30_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_30_21 = s_30_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_30_21).trans round_30_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_30_22 = s_30_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_30_22).trans round_30_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell3019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell3019.canon3
  · exact PV_RunJoin_ValidatorCell3019.canon5
  · exact PV_RunJoin_ValidatorCell3019.canon7
  · exact PV_RunJoin_ValidatorCell3019.canon9
  · exact PV_RunJoin_ValidatorCell3019.canon11
  · exact PV_RunJoin_ValidatorCell3019.canon13
  · exact PV_RunJoin_ValidatorCell3019.canon15
  · exact PV_RunJoin_ValidatorCell3019.canon17
  · exact PV_RunJoin_ValidatorCell3019.canon19
  · exact PV_RunJoin_ValidatorCell3019.canon21
  · exact PV_RunJoin_ValidatorCell3019.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3019.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell3019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell3019.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell3019.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell3019.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell3019.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell3019.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell3019.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell3019.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell3019.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell3019.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell3019.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell3019.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell3019.certificate.pre PV_RunJoin_BankCell3019.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell3019.certificate.pre PV_RunJoin_BankCell3019.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell3019.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell3020

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell3120
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell3119.certificate.pre) i +
    (liftA PV_RunJoin_BankCell3119.certificate.absorption) i else (liftA PV_RunJoin_BankCell3119.certificate.pre) i) = s_31_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 1 = s_31_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell3119.certificate.pre) (liftA PV_RunJoin_BankCell3119.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_31_1,round_31_2]
  exact round_31_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 2 = s_31_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_31_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_31_3 = s_31_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_31_3).trans round_31_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_31_4 = s_31_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_31_4).trans round_31_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 3 = s_31_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_31_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_31_5 = s_31_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_31_5).trans round_31_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_31_6 = s_31_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_31_6).trans round_31_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 4 = s_31_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_31_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_31_7 = s_31_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_31_7).trans round_31_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_31_8 = s_31_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_31_8).trans round_31_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 5 = s_31_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_31_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_31_9 = s_31_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_31_9).trans round_31_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_31_10 = s_31_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_31_10).trans round_31_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 6 = s_31_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_31_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_31_11 = s_31_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_31_11).trans round_31_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_31_12 = s_31_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_31_12).trans round_31_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 7 = s_31_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_31_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_31_13 = s_31_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_31_13).trans round_31_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_31_14 = s_31_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_31_14).trans round_31_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 8 = s_31_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_31_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_31_15 = s_31_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_31_15).trans round_31_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_31_16 = s_31_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_31_16).trans round_31_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 9 = s_31_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_31_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_31_17 = s_31_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_31_17).trans round_31_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_31_18 = s_31_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_31_18).trans round_31_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 10 = s_31_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_31_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_31_19 = s_31_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_31_19).trans round_31_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_31_20 = s_31_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_31_20).trans round_31_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) 11 = s_31_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_31_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_31_21 = s_31_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_31_21).trans round_31_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_31_22 = s_31_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_31_22).trans round_31_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell3119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell3119.canon3
  · exact PV_RunJoin_ValidatorCell3119.canon5
  · exact PV_RunJoin_ValidatorCell3119.canon7
  · exact PV_RunJoin_ValidatorCell3119.canon9
  · exact PV_RunJoin_ValidatorCell3119.canon11
  · exact PV_RunJoin_ValidatorCell3119.canon13
  · exact PV_RunJoin_ValidatorCell3119.canon15
  · exact PV_RunJoin_ValidatorCell3119.canon17
  · exact PV_RunJoin_ValidatorCell3119.canon19
  · exact PV_RunJoin_ValidatorCell3119.canon21
  · exact PV_RunJoin_ValidatorCell3119.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3119.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell3119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell3119.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell3119.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell3119.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell3119.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell3119.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell3119.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell3119.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell3119.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell3119.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell3119.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell3119.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell3119.certificate.pre PV_RunJoin_BankCell3119.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell3119.certificate.pre PV_RunJoin_BankCell3119.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell3119.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell3120

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell3220
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell3219.certificate.pre) i +
    (liftA PV_RunJoin_BankCell3219.certificate.absorption) i else (liftA PV_RunJoin_BankCell3219.certificate.pre) i) = s_32_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 1 = s_32_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell3219.certificate.pre) (liftA PV_RunJoin_BankCell3219.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_32_1,round_32_2]
  exact round_32_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 2 = s_32_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_32_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_32_3 = s_32_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_32_3).trans round_32_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_32_4 = s_32_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_32_4).trans round_32_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 3 = s_32_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_32_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_32_5 = s_32_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_32_5).trans round_32_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_32_6 = s_32_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_32_6).trans round_32_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 4 = s_32_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_32_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_32_7 = s_32_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_32_7).trans round_32_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_32_8 = s_32_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_32_8).trans round_32_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 5 = s_32_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_32_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_32_9 = s_32_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_32_9).trans round_32_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_32_10 = s_32_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_32_10).trans round_32_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 6 = s_32_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_32_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_32_11 = s_32_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_32_11).trans round_32_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_32_12 = s_32_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_32_12).trans round_32_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 7 = s_32_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_32_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_32_13 = s_32_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_32_13).trans round_32_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_32_14 = s_32_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_32_14).trans round_32_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 8 = s_32_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_32_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_32_15 = s_32_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_32_15).trans round_32_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_32_16 = s_32_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_32_16).trans round_32_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 9 = s_32_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_32_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_32_17 = s_32_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_32_17).trans round_32_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_32_18 = s_32_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_32_18).trans round_32_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 10 = s_32_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_32_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_32_19 = s_32_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_32_19).trans round_32_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_32_20 = s_32_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_32_20).trans round_32_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) 11 = s_32_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_32_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_32_21 = s_32_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_32_21).trans round_32_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_32_22 = s_32_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_32_22).trans round_32_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell3219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell3219.canon3
  · exact PV_RunJoin_ValidatorCell3219.canon5
  · exact PV_RunJoin_ValidatorCell3219.canon7
  · exact PV_RunJoin_ValidatorCell3219.canon9
  · exact PV_RunJoin_ValidatorCell3219.canon11
  · exact PV_RunJoin_ValidatorCell3219.canon13
  · exact PV_RunJoin_ValidatorCell3219.canon15
  · exact PV_RunJoin_ValidatorCell3219.canon17
  · exact PV_RunJoin_ValidatorCell3219.canon19
  · exact PV_RunJoin_ValidatorCell3219.canon21
  · exact PV_RunJoin_ValidatorCell3219.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3219.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell3219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell3219.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell3219.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell3219.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell3219.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell3219.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell3219.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell3219.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell3219.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell3219.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell3219.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell3219.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell3219.certificate.pre PV_RunJoin_BankCell3219.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell3219.certificate.pre PV_RunJoin_BankCell3219.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell3219.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell3220

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell3320
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell3319.certificate.pre) i +
    (liftA PV_RunJoin_BankCell3319.certificate.absorption) i else (liftA PV_RunJoin_BankCell3319.certificate.pre) i) = s_33_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 1 = s_33_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell3319.certificate.pre) (liftA PV_RunJoin_BankCell3319.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_33_1,round_33_2]
  exact round_33_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 2 = s_33_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_33_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_33_3 = s_33_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_33_3).trans round_33_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_33_4 = s_33_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_33_4).trans round_33_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 3 = s_33_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_33_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_33_5 = s_33_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_33_5).trans round_33_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_33_6 = s_33_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_33_6).trans round_33_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 4 = s_33_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_33_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_33_7 = s_33_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_33_7).trans round_33_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_33_8 = s_33_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_33_8).trans round_33_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 5 = s_33_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_33_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_33_9 = s_33_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_33_9).trans round_33_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_33_10 = s_33_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_33_10).trans round_33_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 6 = s_33_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_33_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_33_11 = s_33_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_33_11).trans round_33_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_33_12 = s_33_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_33_12).trans round_33_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 7 = s_33_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_33_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_33_13 = s_33_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_33_13).trans round_33_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_33_14 = s_33_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_33_14).trans round_33_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 8 = s_33_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_33_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_33_15 = s_33_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_33_15).trans round_33_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_33_16 = s_33_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_33_16).trans round_33_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 9 = s_33_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_33_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_33_17 = s_33_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_33_17).trans round_33_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_33_18 = s_33_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_33_18).trans round_33_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 10 = s_33_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_33_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_33_19 = s_33_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_33_19).trans round_33_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_33_20 = s_33_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_33_20).trans round_33_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) 11 = s_33_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_33_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_33_21 = s_33_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_33_21).trans round_33_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_33_22 = s_33_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_33_22).trans round_33_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell3319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell3319.canon3
  · exact PV_RunJoin_ValidatorCell3319.canon5
  · exact PV_RunJoin_ValidatorCell3319.canon7
  · exact PV_RunJoin_ValidatorCell3319.canon9
  · exact PV_RunJoin_ValidatorCell3319.canon11
  · exact PV_RunJoin_ValidatorCell3319.canon13
  · exact PV_RunJoin_ValidatorCell3319.canon15
  · exact PV_RunJoin_ValidatorCell3319.canon17
  · exact PV_RunJoin_ValidatorCell3319.canon19
  · exact PV_RunJoin_ValidatorCell3319.canon21
  · exact PV_RunJoin_ValidatorCell3319.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3319.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell3319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell3319.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell3319.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell3319.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell3319.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell3319.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell3319.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell3319.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell3319.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell3319.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell3319.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell3319.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell3319.certificate.pre PV_RunJoin_BankCell3319.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell3319.certificate.pre PV_RunJoin_BankCell3319.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell3319.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell3320

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell3420
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell3419.certificate.pre) i +
    (liftA PV_RunJoin_BankCell3419.certificate.absorption) i else (liftA PV_RunJoin_BankCell3419.certificate.pre) i) = s_34_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 1 = s_34_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell3419.certificate.pre) (liftA PV_RunJoin_BankCell3419.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_34_1,round_34_2]
  exact round_34_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 2 = s_34_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_34_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_34_3 = s_34_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_34_3).trans round_34_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_34_4 = s_34_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_34_4).trans round_34_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 3 = s_34_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_34_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_34_5 = s_34_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_34_5).trans round_34_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_34_6 = s_34_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_34_6).trans round_34_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 4 = s_34_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_34_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_34_7 = s_34_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_34_7).trans round_34_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_34_8 = s_34_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_34_8).trans round_34_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 5 = s_34_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_34_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_34_9 = s_34_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_34_9).trans round_34_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_34_10 = s_34_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_34_10).trans round_34_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 6 = s_34_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_34_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_34_11 = s_34_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_34_11).trans round_34_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_34_12 = s_34_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_34_12).trans round_34_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 7 = s_34_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_34_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_34_13 = s_34_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_34_13).trans round_34_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_34_14 = s_34_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_34_14).trans round_34_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 8 = s_34_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_34_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_34_15 = s_34_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_34_15).trans round_34_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_34_16 = s_34_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_34_16).trans round_34_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 9 = s_34_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_34_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_34_17 = s_34_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_34_17).trans round_34_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_34_18 = s_34_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_34_18).trans round_34_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 10 = s_34_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_34_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_34_19 = s_34_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_34_19).trans round_34_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_34_20 = s_34_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_34_20).trans round_34_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) 11 = s_34_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_34_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_34_21 = s_34_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_34_21).trans round_34_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_34_22 = s_34_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_34_22).trans round_34_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell3419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell3419.canon3
  · exact PV_RunJoin_ValidatorCell3419.canon5
  · exact PV_RunJoin_ValidatorCell3419.canon7
  · exact PV_RunJoin_ValidatorCell3419.canon9
  · exact PV_RunJoin_ValidatorCell3419.canon11
  · exact PV_RunJoin_ValidatorCell3419.canon13
  · exact PV_RunJoin_ValidatorCell3419.canon15
  · exact PV_RunJoin_ValidatorCell3419.canon17
  · exact PV_RunJoin_ValidatorCell3419.canon19
  · exact PV_RunJoin_ValidatorCell3419.canon21
  · exact PV_RunJoin_ValidatorCell3419.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3419.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell3419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell3419.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell3419.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell3419.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell3419.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell3419.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell3419.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell3419.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell3419.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell3419.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell3419.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell3419.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell3419.certificate.pre PV_RunJoin_BankCell3419.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell3419.certificate.pre PV_RunJoin_BankCell3419.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell3419.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell3420

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell3520
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell3519.certificate.pre) i +
    (liftA PV_RunJoin_BankCell3519.certificate.absorption) i else (liftA PV_RunJoin_BankCell3519.certificate.pre) i) = s_35_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 1 = s_35_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell3519.certificate.pre) (liftA PV_RunJoin_BankCell3519.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_35_1,round_35_2]
  exact round_35_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 2 = s_35_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_35_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_35_3 = s_35_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_35_3).trans round_35_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_35_4 = s_35_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_35_4).trans round_35_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 3 = s_35_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_35_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_35_5 = s_35_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_35_5).trans round_35_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_35_6 = s_35_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_35_6).trans round_35_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 4 = s_35_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_35_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_35_7 = s_35_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_35_7).trans round_35_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_35_8 = s_35_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_35_8).trans round_35_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 5 = s_35_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_35_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_35_9 = s_35_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_35_9).trans round_35_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_35_10 = s_35_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_35_10).trans round_35_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 6 = s_35_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_35_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_35_11 = s_35_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_35_11).trans round_35_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_35_12 = s_35_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_35_12).trans round_35_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 7 = s_35_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_35_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_35_13 = s_35_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_35_13).trans round_35_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_35_14 = s_35_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_35_14).trans round_35_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 8 = s_35_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_35_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_35_15 = s_35_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_35_15).trans round_35_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_35_16 = s_35_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_35_16).trans round_35_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 9 = s_35_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_35_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_35_17 = s_35_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_35_17).trans round_35_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_35_18 = s_35_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_35_18).trans round_35_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 10 = s_35_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_35_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_35_19 = s_35_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_35_19).trans round_35_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_35_20 = s_35_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_35_20).trans round_35_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) 11 = s_35_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_35_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_35_21 = s_35_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_35_21).trans round_35_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_35_22 = s_35_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_35_22).trans round_35_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell3519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell3519.canon3
  · exact PV_RunJoin_ValidatorCell3519.canon5
  · exact PV_RunJoin_ValidatorCell3519.canon7
  · exact PV_RunJoin_ValidatorCell3519.canon9
  · exact PV_RunJoin_ValidatorCell3519.canon11
  · exact PV_RunJoin_ValidatorCell3519.canon13
  · exact PV_RunJoin_ValidatorCell3519.canon15
  · exact PV_RunJoin_ValidatorCell3519.canon17
  · exact PV_RunJoin_ValidatorCell3519.canon19
  · exact PV_RunJoin_ValidatorCell3519.canon21
  · exact PV_RunJoin_ValidatorCell3519.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell3519.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell3519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell3519.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell3519.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell3519.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell3519.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell3519.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell3519.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell3519.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell3519.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell3519.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell3519.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell3519.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell3519.certificate.pre PV_RunJoin_BankCell3519.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell3519.certificate.pre PV_RunJoin_BankCell3519.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell3519.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell3520
