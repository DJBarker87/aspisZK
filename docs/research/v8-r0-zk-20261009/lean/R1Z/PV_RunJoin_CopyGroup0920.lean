import R1Z.PV_RunJoin_CopyCertificate20
import R1Z.PV_RunJoin_BankCells0919
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell0920
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell0919.certificate.pre) i +
    (liftA PV_RunJoin_BankCell0919.certificate.absorption) i else (liftA PV_RunJoin_BankCell0919.certificate.pre) i) = s_9_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 1 = s_9_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell0919.certificate.pre) (liftA PV_RunJoin_BankCell0919.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_9_1,round_9_2]
  exact round_9_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 2 = s_9_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_9_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_9_3 = s_9_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_9_3).trans round_9_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_9_4 = s_9_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_9_4).trans round_9_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 3 = s_9_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_9_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_9_5 = s_9_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_9_5).trans round_9_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_9_6 = s_9_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_9_6).trans round_9_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 4 = s_9_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_9_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_9_7 = s_9_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_9_7).trans round_9_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_9_8 = s_9_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_9_8).trans round_9_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 5 = s_9_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_9_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_9_9 = s_9_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_9_9).trans round_9_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_9_10 = s_9_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_9_10).trans round_9_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 6 = s_9_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_9_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_9_11 = s_9_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_9_11).trans round_9_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_9_12 = s_9_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_9_12).trans round_9_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 7 = s_9_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_9_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_9_13 = s_9_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_9_13).trans round_9_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_9_14 = s_9_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_9_14).trans round_9_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 8 = s_9_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_9_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_9_15 = s_9_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_9_15).trans round_9_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_9_16 = s_9_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_9_16).trans round_9_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 9 = s_9_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_9_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_9_17 = s_9_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_9_17).trans round_9_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_9_18 = s_9_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_9_18).trans round_9_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 10 = s_9_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_9_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_9_19 = s_9_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_9_19).trans round_9_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_9_20 = s_9_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_9_20).trans round_9_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) 11 = s_9_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_9_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_9_21 = s_9_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_9_21).trans round_9_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_9_22 = s_9_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_9_22).trans round_9_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell0919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell0919.canon3
  · exact PV_RunJoin_ValidatorCell0919.canon5
  · exact PV_RunJoin_ValidatorCell0919.canon7
  · exact PV_RunJoin_ValidatorCell0919.canon9
  · exact PV_RunJoin_ValidatorCell0919.canon11
  · exact PV_RunJoin_ValidatorCell0919.canon13
  · exact PV_RunJoin_ValidatorCell0919.canon15
  · exact PV_RunJoin_ValidatorCell0919.canon17
  · exact PV_RunJoin_ValidatorCell0919.canon19
  · exact PV_RunJoin_ValidatorCell0919.canon21
  · exact PV_RunJoin_ValidatorCell0919.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell0919.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell0919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell0919.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell0919.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell0919.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell0919.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell0919.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell0919.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell0919.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell0919.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell0919.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell0919.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell0919.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell0919.certificate.pre PV_RunJoin_BankCell0919.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell0919.certificate.pre PV_RunJoin_BankCell0919.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell0919.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell0920

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell1020
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell1019.certificate.pre) i +
    (liftA PV_RunJoin_BankCell1019.certificate.absorption) i else (liftA PV_RunJoin_BankCell1019.certificate.pre) i) = s_10_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 1 = s_10_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell1019.certificate.pre) (liftA PV_RunJoin_BankCell1019.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_10_1,round_10_2]
  exact round_10_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 2 = s_10_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_10_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_10_3 = s_10_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_10_3).trans round_10_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_10_4 = s_10_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_10_4).trans round_10_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 3 = s_10_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_10_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_10_5 = s_10_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_10_5).trans round_10_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_10_6 = s_10_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_10_6).trans round_10_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 4 = s_10_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_10_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_10_7 = s_10_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_10_7).trans round_10_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_10_8 = s_10_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_10_8).trans round_10_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 5 = s_10_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_10_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_10_9 = s_10_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_10_9).trans round_10_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_10_10 = s_10_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_10_10).trans round_10_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 6 = s_10_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_10_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_10_11 = s_10_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_10_11).trans round_10_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_10_12 = s_10_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_10_12).trans round_10_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 7 = s_10_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_10_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_10_13 = s_10_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_10_13).trans round_10_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_10_14 = s_10_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_10_14).trans round_10_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 8 = s_10_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_10_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_10_15 = s_10_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_10_15).trans round_10_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_10_16 = s_10_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_10_16).trans round_10_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 9 = s_10_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_10_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_10_17 = s_10_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_10_17).trans round_10_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_10_18 = s_10_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_10_18).trans round_10_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 10 = s_10_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_10_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_10_19 = s_10_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_10_19).trans round_10_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_10_20 = s_10_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_10_20).trans round_10_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) 11 = s_10_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_10_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_10_21 = s_10_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_10_21).trans round_10_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_10_22 = s_10_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_10_22).trans round_10_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell1019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell1019.canon3
  · exact PV_RunJoin_ValidatorCell1019.canon5
  · exact PV_RunJoin_ValidatorCell1019.canon7
  · exact PV_RunJoin_ValidatorCell1019.canon9
  · exact PV_RunJoin_ValidatorCell1019.canon11
  · exact PV_RunJoin_ValidatorCell1019.canon13
  · exact PV_RunJoin_ValidatorCell1019.canon15
  · exact PV_RunJoin_ValidatorCell1019.canon17
  · exact PV_RunJoin_ValidatorCell1019.canon19
  · exact PV_RunJoin_ValidatorCell1019.canon21
  · exact PV_RunJoin_ValidatorCell1019.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1019.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell1019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell1019.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell1019.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell1019.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell1019.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell1019.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell1019.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell1019.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell1019.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell1019.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell1019.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell1019.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell1019.certificate.pre PV_RunJoin_BankCell1019.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell1019.certificate.pre PV_RunJoin_BankCell1019.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell1019.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell1020

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell1120
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell1119.certificate.pre) i +
    (liftA PV_RunJoin_BankCell1119.certificate.absorption) i else (liftA PV_RunJoin_BankCell1119.certificate.pre) i) = s_11_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 1 = s_11_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell1119.certificate.pre) (liftA PV_RunJoin_BankCell1119.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_11_1,round_11_2]
  exact round_11_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 2 = s_11_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_11_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_11_3 = s_11_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_11_3).trans round_11_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_11_4 = s_11_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_11_4).trans round_11_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 3 = s_11_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_11_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_11_5 = s_11_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_11_5).trans round_11_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_11_6 = s_11_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_11_6).trans round_11_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 4 = s_11_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_11_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_11_7 = s_11_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_11_7).trans round_11_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_11_8 = s_11_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_11_8).trans round_11_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 5 = s_11_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_11_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_11_9 = s_11_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_11_9).trans round_11_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_11_10 = s_11_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_11_10).trans round_11_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 6 = s_11_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_11_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_11_11 = s_11_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_11_11).trans round_11_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_11_12 = s_11_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_11_12).trans round_11_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 7 = s_11_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_11_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_11_13 = s_11_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_11_13).trans round_11_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_11_14 = s_11_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_11_14).trans round_11_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 8 = s_11_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_11_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_11_15 = s_11_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_11_15).trans round_11_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_11_16 = s_11_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_11_16).trans round_11_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 9 = s_11_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_11_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_11_17 = s_11_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_11_17).trans round_11_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_11_18 = s_11_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_11_18).trans round_11_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 10 = s_11_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_11_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_11_19 = s_11_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_11_19).trans round_11_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_11_20 = s_11_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_11_20).trans round_11_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) 11 = s_11_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_11_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_11_21 = s_11_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_11_21).trans round_11_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_11_22 = s_11_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_11_22).trans round_11_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell1119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell1119.canon3
  · exact PV_RunJoin_ValidatorCell1119.canon5
  · exact PV_RunJoin_ValidatorCell1119.canon7
  · exact PV_RunJoin_ValidatorCell1119.canon9
  · exact PV_RunJoin_ValidatorCell1119.canon11
  · exact PV_RunJoin_ValidatorCell1119.canon13
  · exact PV_RunJoin_ValidatorCell1119.canon15
  · exact PV_RunJoin_ValidatorCell1119.canon17
  · exact PV_RunJoin_ValidatorCell1119.canon19
  · exact PV_RunJoin_ValidatorCell1119.canon21
  · exact PV_RunJoin_ValidatorCell1119.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1119.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell1119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell1119.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell1119.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell1119.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell1119.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell1119.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell1119.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell1119.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell1119.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell1119.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell1119.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell1119.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell1119.certificate.pre PV_RunJoin_BankCell1119.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell1119.certificate.pre PV_RunJoin_BankCell1119.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell1119.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell1120

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell1220
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell1219.certificate.pre) i +
    (liftA PV_RunJoin_BankCell1219.certificate.absorption) i else (liftA PV_RunJoin_BankCell1219.certificate.pre) i) = s_12_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 1 = s_12_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell1219.certificate.pre) (liftA PV_RunJoin_BankCell1219.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_12_1,round_12_2]
  exact round_12_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 2 = s_12_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_12_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_12_3 = s_12_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_12_3).trans round_12_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_12_4 = s_12_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_12_4).trans round_12_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 3 = s_12_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_12_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_12_5 = s_12_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_12_5).trans round_12_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_12_6 = s_12_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_12_6).trans round_12_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 4 = s_12_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_12_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_12_7 = s_12_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_12_7).trans round_12_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_12_8 = s_12_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_12_8).trans round_12_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 5 = s_12_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_12_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_12_9 = s_12_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_12_9).trans round_12_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_12_10 = s_12_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_12_10).trans round_12_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 6 = s_12_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_12_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_12_11 = s_12_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_12_11).trans round_12_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_12_12 = s_12_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_12_12).trans round_12_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 7 = s_12_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_12_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_12_13 = s_12_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_12_13).trans round_12_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_12_14 = s_12_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_12_14).trans round_12_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 8 = s_12_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_12_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_12_15 = s_12_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_12_15).trans round_12_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_12_16 = s_12_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_12_16).trans round_12_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 9 = s_12_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_12_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_12_17 = s_12_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_12_17).trans round_12_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_12_18 = s_12_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_12_18).trans round_12_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 10 = s_12_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_12_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_12_19 = s_12_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_12_19).trans round_12_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_12_20 = s_12_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_12_20).trans round_12_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) 11 = s_12_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_12_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_12_21 = s_12_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_12_21).trans round_12_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_12_22 = s_12_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_12_22).trans round_12_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell1219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell1219.canon3
  · exact PV_RunJoin_ValidatorCell1219.canon5
  · exact PV_RunJoin_ValidatorCell1219.canon7
  · exact PV_RunJoin_ValidatorCell1219.canon9
  · exact PV_RunJoin_ValidatorCell1219.canon11
  · exact PV_RunJoin_ValidatorCell1219.canon13
  · exact PV_RunJoin_ValidatorCell1219.canon15
  · exact PV_RunJoin_ValidatorCell1219.canon17
  · exact PV_RunJoin_ValidatorCell1219.canon19
  · exact PV_RunJoin_ValidatorCell1219.canon21
  · exact PV_RunJoin_ValidatorCell1219.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1219.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell1219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell1219.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell1219.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell1219.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell1219.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell1219.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell1219.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell1219.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell1219.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell1219.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell1219.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell1219.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell1219.certificate.pre PV_RunJoin_BankCell1219.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell1219.certificate.pre PV_RunJoin_BankCell1219.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell1219.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell1220

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell1320
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell1319.certificate.pre) i +
    (liftA PV_RunJoin_BankCell1319.certificate.absorption) i else (liftA PV_RunJoin_BankCell1319.certificate.pre) i) = s_13_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 1 = s_13_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell1319.certificate.pre) (liftA PV_RunJoin_BankCell1319.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_13_1,round_13_2]
  exact round_13_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 2 = s_13_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_13_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_13_3 = s_13_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_13_3).trans round_13_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_13_4 = s_13_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_13_4).trans round_13_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 3 = s_13_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_13_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_13_5 = s_13_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_13_5).trans round_13_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_13_6 = s_13_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_13_6).trans round_13_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 4 = s_13_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_13_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_13_7 = s_13_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_13_7).trans round_13_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_13_8 = s_13_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_13_8).trans round_13_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 5 = s_13_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_13_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_13_9 = s_13_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_13_9).trans round_13_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_13_10 = s_13_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_13_10).trans round_13_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 6 = s_13_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_13_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_13_11 = s_13_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_13_11).trans round_13_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_13_12 = s_13_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_13_12).trans round_13_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 7 = s_13_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_13_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_13_13 = s_13_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_13_13).trans round_13_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_13_14 = s_13_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_13_14).trans round_13_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 8 = s_13_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_13_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_13_15 = s_13_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_13_15).trans round_13_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_13_16 = s_13_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_13_16).trans round_13_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 9 = s_13_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_13_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_13_17 = s_13_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_13_17).trans round_13_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_13_18 = s_13_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_13_18).trans round_13_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 10 = s_13_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_13_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_13_19 = s_13_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_13_19).trans round_13_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_13_20 = s_13_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_13_20).trans round_13_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) 11 = s_13_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_13_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_13_21 = s_13_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_13_21).trans round_13_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_13_22 = s_13_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_13_22).trans round_13_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell1319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell1319.canon3
  · exact PV_RunJoin_ValidatorCell1319.canon5
  · exact PV_RunJoin_ValidatorCell1319.canon7
  · exact PV_RunJoin_ValidatorCell1319.canon9
  · exact PV_RunJoin_ValidatorCell1319.canon11
  · exact PV_RunJoin_ValidatorCell1319.canon13
  · exact PV_RunJoin_ValidatorCell1319.canon15
  · exact PV_RunJoin_ValidatorCell1319.canon17
  · exact PV_RunJoin_ValidatorCell1319.canon19
  · exact PV_RunJoin_ValidatorCell1319.canon21
  · exact PV_RunJoin_ValidatorCell1319.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1319.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell1319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell1319.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell1319.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell1319.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell1319.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell1319.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell1319.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell1319.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell1319.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell1319.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell1319.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell1319.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell1319.certificate.pre PV_RunJoin_BankCell1319.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell1319.certificate.pre PV_RunJoin_BankCell1319.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell1319.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell1320

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell1420
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell1419.certificate.pre) i +
    (liftA PV_RunJoin_BankCell1419.certificate.absorption) i else (liftA PV_RunJoin_BankCell1419.certificate.pre) i) = s_14_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 1 = s_14_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell1419.certificate.pre) (liftA PV_RunJoin_BankCell1419.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_14_1,round_14_2]
  exact round_14_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 2 = s_14_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_14_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_14_3 = s_14_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_14_3).trans round_14_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_14_4 = s_14_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_14_4).trans round_14_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 3 = s_14_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_14_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_14_5 = s_14_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_14_5).trans round_14_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_14_6 = s_14_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_14_6).trans round_14_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 4 = s_14_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_14_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_14_7 = s_14_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_14_7).trans round_14_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_14_8 = s_14_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_14_8).trans round_14_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 5 = s_14_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_14_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_14_9 = s_14_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_14_9).trans round_14_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_14_10 = s_14_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_14_10).trans round_14_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 6 = s_14_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_14_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_14_11 = s_14_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_14_11).trans round_14_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_14_12 = s_14_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_14_12).trans round_14_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 7 = s_14_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_14_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_14_13 = s_14_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_14_13).trans round_14_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_14_14 = s_14_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_14_14).trans round_14_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 8 = s_14_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_14_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_14_15 = s_14_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_14_15).trans round_14_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_14_16 = s_14_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_14_16).trans round_14_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 9 = s_14_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_14_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_14_17 = s_14_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_14_17).trans round_14_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_14_18 = s_14_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_14_18).trans round_14_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 10 = s_14_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_14_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_14_19 = s_14_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_14_19).trans round_14_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_14_20 = s_14_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_14_20).trans round_14_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) 11 = s_14_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_14_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_14_21 = s_14_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_14_21).trans round_14_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_14_22 = s_14_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_14_22).trans round_14_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell1419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell1419.canon3
  · exact PV_RunJoin_ValidatorCell1419.canon5
  · exact PV_RunJoin_ValidatorCell1419.canon7
  · exact PV_RunJoin_ValidatorCell1419.canon9
  · exact PV_RunJoin_ValidatorCell1419.canon11
  · exact PV_RunJoin_ValidatorCell1419.canon13
  · exact PV_RunJoin_ValidatorCell1419.canon15
  · exact PV_RunJoin_ValidatorCell1419.canon17
  · exact PV_RunJoin_ValidatorCell1419.canon19
  · exact PV_RunJoin_ValidatorCell1419.canon21
  · exact PV_RunJoin_ValidatorCell1419.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1419.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell1419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell1419.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell1419.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell1419.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell1419.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell1419.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell1419.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell1419.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell1419.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell1419.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell1419.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell1419.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell1419.certificate.pre PV_RunJoin_BankCell1419.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell1419.certificate.pre PV_RunJoin_BankCell1419.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell1419.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell1420

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell1520
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell1519.certificate.pre) i +
    (liftA PV_RunJoin_BankCell1519.certificate.absorption) i else (liftA PV_RunJoin_BankCell1519.certificate.pre) i) = s_15_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 1 = s_15_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell1519.certificate.pre) (liftA PV_RunJoin_BankCell1519.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_15_1,round_15_2]
  exact round_15_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 2 = s_15_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_15_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_15_3 = s_15_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_15_3).trans round_15_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_15_4 = s_15_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_15_4).trans round_15_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 3 = s_15_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_15_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_15_5 = s_15_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_15_5).trans round_15_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_15_6 = s_15_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_15_6).trans round_15_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 4 = s_15_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_15_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_15_7 = s_15_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_15_7).trans round_15_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_15_8 = s_15_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_15_8).trans round_15_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 5 = s_15_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_15_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_15_9 = s_15_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_15_9).trans round_15_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_15_10 = s_15_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_15_10).trans round_15_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 6 = s_15_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_15_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_15_11 = s_15_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_15_11).trans round_15_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_15_12 = s_15_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_15_12).trans round_15_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 7 = s_15_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_15_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_15_13 = s_15_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_15_13).trans round_15_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_15_14 = s_15_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_15_14).trans round_15_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 8 = s_15_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_15_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_15_15 = s_15_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_15_15).trans round_15_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_15_16 = s_15_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_15_16).trans round_15_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 9 = s_15_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_15_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_15_17 = s_15_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_15_17).trans round_15_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_15_18 = s_15_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_15_18).trans round_15_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 10 = s_15_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_15_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_15_19 = s_15_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_15_19).trans round_15_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_15_20 = s_15_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_15_20).trans round_15_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) 11 = s_15_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_15_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_15_21 = s_15_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_15_21).trans round_15_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_15_22 = s_15_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_15_22).trans round_15_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell1519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell1519.canon3
  · exact PV_RunJoin_ValidatorCell1519.canon5
  · exact PV_RunJoin_ValidatorCell1519.canon7
  · exact PV_RunJoin_ValidatorCell1519.canon9
  · exact PV_RunJoin_ValidatorCell1519.canon11
  · exact PV_RunJoin_ValidatorCell1519.canon13
  · exact PV_RunJoin_ValidatorCell1519.canon15
  · exact PV_RunJoin_ValidatorCell1519.canon17
  · exact PV_RunJoin_ValidatorCell1519.canon19
  · exact PV_RunJoin_ValidatorCell1519.canon21
  · exact PV_RunJoin_ValidatorCell1519.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1519.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell1519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell1519.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell1519.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell1519.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell1519.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell1519.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell1519.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell1519.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell1519.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell1519.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell1519.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell1519.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell1519.certificate.pre PV_RunJoin_BankCell1519.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell1519.certificate.pre PV_RunJoin_BankCell1519.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell1519.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell1520

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell1620
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell1619.certificate.pre) i +
    (liftA PV_RunJoin_BankCell1619.certificate.absorption) i else (liftA PV_RunJoin_BankCell1619.certificate.pre) i) = s_16_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 1 = s_16_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell1619.certificate.pre) (liftA PV_RunJoin_BankCell1619.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_16_1,round_16_2]
  exact round_16_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 2 = s_16_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_16_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_16_3 = s_16_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_16_3).trans round_16_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_16_4 = s_16_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_16_4).trans round_16_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 3 = s_16_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_16_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_16_5 = s_16_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_16_5).trans round_16_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_16_6 = s_16_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_16_6).trans round_16_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 4 = s_16_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_16_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_16_7 = s_16_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_16_7).trans round_16_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_16_8 = s_16_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_16_8).trans round_16_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 5 = s_16_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_16_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_16_9 = s_16_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_16_9).trans round_16_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_16_10 = s_16_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_16_10).trans round_16_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 6 = s_16_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_16_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_16_11 = s_16_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_16_11).trans round_16_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_16_12 = s_16_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_16_12).trans round_16_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 7 = s_16_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_16_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_16_13 = s_16_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_16_13).trans round_16_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_16_14 = s_16_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_16_14).trans round_16_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 8 = s_16_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_16_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_16_15 = s_16_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_16_15).trans round_16_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_16_16 = s_16_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_16_16).trans round_16_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 9 = s_16_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_16_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_16_17 = s_16_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_16_17).trans round_16_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_16_18 = s_16_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_16_18).trans round_16_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 10 = s_16_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_16_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_16_19 = s_16_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_16_19).trans round_16_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_16_20 = s_16_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_16_20).trans round_16_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) 11 = s_16_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_16_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_16_21 = s_16_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_16_21).trans round_16_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_16_22 = s_16_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_16_22).trans round_16_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell1619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell1619.canon3
  · exact PV_RunJoin_ValidatorCell1619.canon5
  · exact PV_RunJoin_ValidatorCell1619.canon7
  · exact PV_RunJoin_ValidatorCell1619.canon9
  · exact PV_RunJoin_ValidatorCell1619.canon11
  · exact PV_RunJoin_ValidatorCell1619.canon13
  · exact PV_RunJoin_ValidatorCell1619.canon15
  · exact PV_RunJoin_ValidatorCell1619.canon17
  · exact PV_RunJoin_ValidatorCell1619.canon19
  · exact PV_RunJoin_ValidatorCell1619.canon21
  · exact PV_RunJoin_ValidatorCell1619.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1619.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell1619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell1619.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell1619.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell1619.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell1619.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell1619.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell1619.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell1619.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell1619.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell1619.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell1619.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell1619.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell1619.certificate.pre PV_RunJoin_BankCell1619.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell1619.certificate.pre PV_RunJoin_BankCell1619.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell1619.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell1620

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell1720
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell1719.certificate.pre) i +
    (liftA PV_RunJoin_BankCell1719.certificate.absorption) i else (liftA PV_RunJoin_BankCell1719.certificate.pre) i) = s_17_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 1 = s_17_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell1719.certificate.pre) (liftA PV_RunJoin_BankCell1719.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_17_1,round_17_2]
  exact round_17_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 2 = s_17_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_17_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_17_3 = s_17_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_17_3).trans round_17_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_17_4 = s_17_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_17_4).trans round_17_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 3 = s_17_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_17_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_17_5 = s_17_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_17_5).trans round_17_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_17_6 = s_17_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_17_6).trans round_17_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 4 = s_17_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_17_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_17_7 = s_17_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_17_7).trans round_17_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_17_8 = s_17_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_17_8).trans round_17_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 5 = s_17_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_17_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_17_9 = s_17_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_17_9).trans round_17_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_17_10 = s_17_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_17_10).trans round_17_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 6 = s_17_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_17_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_17_11 = s_17_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_17_11).trans round_17_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_17_12 = s_17_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_17_12).trans round_17_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 7 = s_17_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_17_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_17_13 = s_17_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_17_13).trans round_17_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_17_14 = s_17_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_17_14).trans round_17_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 8 = s_17_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_17_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_17_15 = s_17_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_17_15).trans round_17_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_17_16 = s_17_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_17_16).trans round_17_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 9 = s_17_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_17_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_17_17 = s_17_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_17_17).trans round_17_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_17_18 = s_17_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_17_18).trans round_17_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 10 = s_17_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_17_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_17_19 = s_17_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_17_19).trans round_17_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_17_20 = s_17_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_17_20).trans round_17_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) 11 = s_17_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_17_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_17_21 = s_17_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_17_21).trans round_17_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_17_22 = s_17_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_17_22).trans round_17_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell1719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell1719.canon3
  · exact PV_RunJoin_ValidatorCell1719.canon5
  · exact PV_RunJoin_ValidatorCell1719.canon7
  · exact PV_RunJoin_ValidatorCell1719.canon9
  · exact PV_RunJoin_ValidatorCell1719.canon11
  · exact PV_RunJoin_ValidatorCell1719.canon13
  · exact PV_RunJoin_ValidatorCell1719.canon15
  · exact PV_RunJoin_ValidatorCell1719.canon17
  · exact PV_RunJoin_ValidatorCell1719.canon19
  · exact PV_RunJoin_ValidatorCell1719.canon21
  · exact PV_RunJoin_ValidatorCell1719.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1719.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell1719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell1719.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell1719.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell1719.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell1719.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell1719.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell1719.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell1719.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell1719.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell1719.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell1719.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell1719.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell1719.certificate.pre PV_RunJoin_BankCell1719.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell1719.certificate.pre PV_RunJoin_BankCell1719.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell1719.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell1720
