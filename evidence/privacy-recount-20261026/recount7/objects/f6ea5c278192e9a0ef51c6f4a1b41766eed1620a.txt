import R1Z.PV_RunJoin_CopyCertificate20
import R1Z.PV_RunJoin_BankCells7219
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell7220
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell7219.certificate.pre) i +
    (liftA PV_RunJoin_BankCell7219.certificate.absorption) i else (liftA PV_RunJoin_BankCell7219.certificate.pre) i) = s_72_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 1 = s_72_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell7219.certificate.pre) (liftA PV_RunJoin_BankCell7219.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_72_1,round_72_2]
  exact round_72_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 2 = s_72_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_72_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_72_3 = s_72_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_72_3).trans round_72_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_72_4 = s_72_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_72_4).trans round_72_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 3 = s_72_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_72_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_72_5 = s_72_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_72_5).trans round_72_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_72_6 = s_72_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_72_6).trans round_72_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 4 = s_72_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_72_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_72_7 = s_72_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_72_7).trans round_72_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_72_8 = s_72_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_72_8).trans round_72_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 5 = s_72_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_72_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_72_9 = s_72_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_72_9).trans round_72_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_72_10 = s_72_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_72_10).trans round_72_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 6 = s_72_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_72_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_72_11 = s_72_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_72_11).trans round_72_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_72_12 = s_72_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_72_12).trans round_72_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 7 = s_72_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_72_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_72_13 = s_72_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_72_13).trans round_72_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_72_14 = s_72_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_72_14).trans round_72_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 8 = s_72_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_72_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_72_15 = s_72_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_72_15).trans round_72_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_72_16 = s_72_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_72_16).trans round_72_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 9 = s_72_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_72_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_72_17 = s_72_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_72_17).trans round_72_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_72_18 = s_72_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_72_18).trans round_72_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 10 = s_72_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_72_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_72_19 = s_72_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_72_19).trans round_72_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_72_20 = s_72_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_72_20).trans round_72_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) 11 = s_72_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_72_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_72_21 = s_72_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_72_21).trans round_72_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_72_22 = s_72_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_72_22).trans round_72_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell7219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell7219.canon3
  · exact PV_RunJoin_ValidatorCell7219.canon5
  · exact PV_RunJoin_ValidatorCell7219.canon7
  · exact PV_RunJoin_ValidatorCell7219.canon9
  · exact PV_RunJoin_ValidatorCell7219.canon11
  · exact PV_RunJoin_ValidatorCell7219.canon13
  · exact PV_RunJoin_ValidatorCell7219.canon15
  · exact PV_RunJoin_ValidatorCell7219.canon17
  · exact PV_RunJoin_ValidatorCell7219.canon19
  · exact PV_RunJoin_ValidatorCell7219.canon21
  · exact PV_RunJoin_ValidatorCell7219.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7219.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell7219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell7219.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell7219.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell7219.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell7219.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell7219.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell7219.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell7219.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell7219.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell7219.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell7219.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell7219.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell7219.certificate.pre PV_RunJoin_BankCell7219.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell7219.certificate.pre PV_RunJoin_BankCell7219.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell7219.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell7220

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell7320
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell7319.certificate.pre) i +
    (liftA PV_RunJoin_BankCell7319.certificate.absorption) i else (liftA PV_RunJoin_BankCell7319.certificate.pre) i) = s_73_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 1 = s_73_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell7319.certificate.pre) (liftA PV_RunJoin_BankCell7319.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_73_1,round_73_2]
  exact round_73_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 2 = s_73_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_73_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_73_3 = s_73_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_73_3).trans round_73_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_73_4 = s_73_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_73_4).trans round_73_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 3 = s_73_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_73_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_73_5 = s_73_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_73_5).trans round_73_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_73_6 = s_73_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_73_6).trans round_73_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 4 = s_73_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_73_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_73_7 = s_73_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_73_7).trans round_73_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_73_8 = s_73_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_73_8).trans round_73_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 5 = s_73_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_73_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_73_9 = s_73_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_73_9).trans round_73_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_73_10 = s_73_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_73_10).trans round_73_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 6 = s_73_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_73_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_73_11 = s_73_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_73_11).trans round_73_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_73_12 = s_73_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_73_12).trans round_73_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 7 = s_73_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_73_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_73_13 = s_73_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_73_13).trans round_73_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_73_14 = s_73_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_73_14).trans round_73_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 8 = s_73_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_73_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_73_15 = s_73_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_73_15).trans round_73_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_73_16 = s_73_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_73_16).trans round_73_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 9 = s_73_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_73_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_73_17 = s_73_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_73_17).trans round_73_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_73_18 = s_73_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_73_18).trans round_73_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 10 = s_73_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_73_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_73_19 = s_73_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_73_19).trans round_73_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_73_20 = s_73_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_73_20).trans round_73_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) 11 = s_73_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_73_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_73_21 = s_73_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_73_21).trans round_73_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_73_22 = s_73_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_73_22).trans round_73_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell7319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell7319.canon3
  · exact PV_RunJoin_ValidatorCell7319.canon5
  · exact PV_RunJoin_ValidatorCell7319.canon7
  · exact PV_RunJoin_ValidatorCell7319.canon9
  · exact PV_RunJoin_ValidatorCell7319.canon11
  · exact PV_RunJoin_ValidatorCell7319.canon13
  · exact PV_RunJoin_ValidatorCell7319.canon15
  · exact PV_RunJoin_ValidatorCell7319.canon17
  · exact PV_RunJoin_ValidatorCell7319.canon19
  · exact PV_RunJoin_ValidatorCell7319.canon21
  · exact PV_RunJoin_ValidatorCell7319.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7319.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell7319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell7319.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell7319.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell7319.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell7319.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell7319.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell7319.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell7319.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell7319.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell7319.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell7319.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell7319.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell7319.certificate.pre PV_RunJoin_BankCell7319.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell7319.certificate.pre PV_RunJoin_BankCell7319.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell7319.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell7320

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell7420
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell7419.certificate.pre) i +
    (liftA PV_RunJoin_BankCell7419.certificate.absorption) i else (liftA PV_RunJoin_BankCell7419.certificate.pre) i) = s_74_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 1 = s_74_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell7419.certificate.pre) (liftA PV_RunJoin_BankCell7419.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_74_1,round_74_2]
  exact round_74_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 2 = s_74_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_74_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_74_3 = s_74_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_74_3).trans round_74_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_74_4 = s_74_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_74_4).trans round_74_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 3 = s_74_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_74_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_74_5 = s_74_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_74_5).trans round_74_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_74_6 = s_74_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_74_6).trans round_74_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 4 = s_74_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_74_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_74_7 = s_74_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_74_7).trans round_74_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_74_8 = s_74_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_74_8).trans round_74_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 5 = s_74_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_74_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_74_9 = s_74_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_74_9).trans round_74_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_74_10 = s_74_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_74_10).trans round_74_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 6 = s_74_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_74_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_74_11 = s_74_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_74_11).trans round_74_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_74_12 = s_74_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_74_12).trans round_74_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 7 = s_74_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_74_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_74_13 = s_74_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_74_13).trans round_74_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_74_14 = s_74_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_74_14).trans round_74_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 8 = s_74_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_74_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_74_15 = s_74_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_74_15).trans round_74_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_74_16 = s_74_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_74_16).trans round_74_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 9 = s_74_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_74_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_74_17 = s_74_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_74_17).trans round_74_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_74_18 = s_74_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_74_18).trans round_74_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 10 = s_74_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_74_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_74_19 = s_74_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_74_19).trans round_74_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_74_20 = s_74_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_74_20).trans round_74_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) 11 = s_74_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_74_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_74_21 = s_74_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_74_21).trans round_74_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_74_22 = s_74_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_74_22).trans round_74_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell7419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell7419.canon3
  · exact PV_RunJoin_ValidatorCell7419.canon5
  · exact PV_RunJoin_ValidatorCell7419.canon7
  · exact PV_RunJoin_ValidatorCell7419.canon9
  · exact PV_RunJoin_ValidatorCell7419.canon11
  · exact PV_RunJoin_ValidatorCell7419.canon13
  · exact PV_RunJoin_ValidatorCell7419.canon15
  · exact PV_RunJoin_ValidatorCell7419.canon17
  · exact PV_RunJoin_ValidatorCell7419.canon19
  · exact PV_RunJoin_ValidatorCell7419.canon21
  · exact PV_RunJoin_ValidatorCell7419.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7419.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell7419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell7419.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell7419.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell7419.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell7419.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell7419.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell7419.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell7419.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell7419.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell7419.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell7419.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell7419.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell7419.certificate.pre PV_RunJoin_BankCell7419.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell7419.certificate.pre PV_RunJoin_BankCell7419.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell7419.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell7420

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell7520
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell7519.certificate.pre) i +
    (liftA PV_RunJoin_BankCell7519.certificate.absorption) i else (liftA PV_RunJoin_BankCell7519.certificate.pre) i) = s_75_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 1 = s_75_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell7519.certificate.pre) (liftA PV_RunJoin_BankCell7519.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_75_1,round_75_2]
  exact round_75_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 2 = s_75_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_75_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_75_3 = s_75_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_75_3).trans round_75_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_75_4 = s_75_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_75_4).trans round_75_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 3 = s_75_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_75_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_75_5 = s_75_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_75_5).trans round_75_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_75_6 = s_75_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_75_6).trans round_75_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 4 = s_75_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_75_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_75_7 = s_75_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_75_7).trans round_75_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_75_8 = s_75_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_75_8).trans round_75_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 5 = s_75_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_75_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_75_9 = s_75_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_75_9).trans round_75_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_75_10 = s_75_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_75_10).trans round_75_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 6 = s_75_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_75_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_75_11 = s_75_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_75_11).trans round_75_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_75_12 = s_75_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_75_12).trans round_75_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 7 = s_75_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_75_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_75_13 = s_75_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_75_13).trans round_75_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_75_14 = s_75_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_75_14).trans round_75_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 8 = s_75_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_75_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_75_15 = s_75_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_75_15).trans round_75_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_75_16 = s_75_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_75_16).trans round_75_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 9 = s_75_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_75_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_75_17 = s_75_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_75_17).trans round_75_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_75_18 = s_75_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_75_18).trans round_75_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 10 = s_75_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_75_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_75_19 = s_75_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_75_19).trans round_75_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_75_20 = s_75_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_75_20).trans round_75_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) 11 = s_75_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_75_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_75_21 = s_75_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_75_21).trans round_75_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_75_22 = s_75_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_75_22).trans round_75_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell7519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell7519.canon3
  · exact PV_RunJoin_ValidatorCell7519.canon5
  · exact PV_RunJoin_ValidatorCell7519.canon7
  · exact PV_RunJoin_ValidatorCell7519.canon9
  · exact PV_RunJoin_ValidatorCell7519.canon11
  · exact PV_RunJoin_ValidatorCell7519.canon13
  · exact PV_RunJoin_ValidatorCell7519.canon15
  · exact PV_RunJoin_ValidatorCell7519.canon17
  · exact PV_RunJoin_ValidatorCell7519.canon19
  · exact PV_RunJoin_ValidatorCell7519.canon21
  · exact PV_RunJoin_ValidatorCell7519.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7519.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell7519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell7519.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell7519.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell7519.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell7519.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell7519.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell7519.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell7519.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell7519.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell7519.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell7519.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell7519.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell7519.certificate.pre PV_RunJoin_BankCell7519.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell7519.certificate.pre PV_RunJoin_BankCell7519.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell7519.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell7520

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell7620
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell7619.certificate.pre) i +
    (liftA PV_RunJoin_BankCell7619.certificate.absorption) i else (liftA PV_RunJoin_BankCell7619.certificate.pre) i) = s_76_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 1 = s_76_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell7619.certificate.pre) (liftA PV_RunJoin_BankCell7619.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_76_1,round_76_2]
  exact round_76_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 2 = s_76_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_76_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_76_3 = s_76_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_76_3).trans round_76_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_76_4 = s_76_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_76_4).trans round_76_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 3 = s_76_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_76_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_76_5 = s_76_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_76_5).trans round_76_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_76_6 = s_76_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_76_6).trans round_76_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 4 = s_76_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_76_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_76_7 = s_76_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_76_7).trans round_76_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_76_8 = s_76_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_76_8).trans round_76_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 5 = s_76_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_76_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_76_9 = s_76_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_76_9).trans round_76_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_76_10 = s_76_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_76_10).trans round_76_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 6 = s_76_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_76_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_76_11 = s_76_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_76_11).trans round_76_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_76_12 = s_76_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_76_12).trans round_76_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 7 = s_76_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_76_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_76_13 = s_76_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_76_13).trans round_76_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_76_14 = s_76_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_76_14).trans round_76_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 8 = s_76_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_76_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_76_15 = s_76_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_76_15).trans round_76_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_76_16 = s_76_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_76_16).trans round_76_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 9 = s_76_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_76_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_76_17 = s_76_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_76_17).trans round_76_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_76_18 = s_76_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_76_18).trans round_76_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 10 = s_76_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_76_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_76_19 = s_76_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_76_19).trans round_76_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_76_20 = s_76_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_76_20).trans round_76_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) 11 = s_76_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_76_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_76_21 = s_76_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_76_21).trans round_76_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_76_22 = s_76_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_76_22).trans round_76_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell7619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell7619.canon3
  · exact PV_RunJoin_ValidatorCell7619.canon5
  · exact PV_RunJoin_ValidatorCell7619.canon7
  · exact PV_RunJoin_ValidatorCell7619.canon9
  · exact PV_RunJoin_ValidatorCell7619.canon11
  · exact PV_RunJoin_ValidatorCell7619.canon13
  · exact PV_RunJoin_ValidatorCell7619.canon15
  · exact PV_RunJoin_ValidatorCell7619.canon17
  · exact PV_RunJoin_ValidatorCell7619.canon19
  · exact PV_RunJoin_ValidatorCell7619.canon21
  · exact PV_RunJoin_ValidatorCell7619.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7619.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell7619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell7619.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell7619.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell7619.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell7619.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell7619.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell7619.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell7619.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell7619.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell7619.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell7619.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell7619.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell7619.certificate.pre PV_RunJoin_BankCell7619.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell7619.certificate.pre PV_RunJoin_BankCell7619.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell7619.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell7620

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell7720
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell7719.certificate.pre) i +
    (liftA PV_RunJoin_BankCell7719.certificate.absorption) i else (liftA PV_RunJoin_BankCell7719.certificate.pre) i) = s_77_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 1 = s_77_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell7719.certificate.pre) (liftA PV_RunJoin_BankCell7719.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_77_1,round_77_2]
  exact round_77_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 2 = s_77_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_77_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_77_3 = s_77_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_77_3).trans round_77_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_77_4 = s_77_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_77_4).trans round_77_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 3 = s_77_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_77_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_77_5 = s_77_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_77_5).trans round_77_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_77_6 = s_77_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_77_6).trans round_77_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 4 = s_77_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_77_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_77_7 = s_77_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_77_7).trans round_77_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_77_8 = s_77_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_77_8).trans round_77_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 5 = s_77_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_77_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_77_9 = s_77_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_77_9).trans round_77_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_77_10 = s_77_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_77_10).trans round_77_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 6 = s_77_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_77_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_77_11 = s_77_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_77_11).trans round_77_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_77_12 = s_77_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_77_12).trans round_77_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 7 = s_77_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_77_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_77_13 = s_77_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_77_13).trans round_77_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_77_14 = s_77_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_77_14).trans round_77_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 8 = s_77_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_77_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_77_15 = s_77_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_77_15).trans round_77_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_77_16 = s_77_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_77_16).trans round_77_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 9 = s_77_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_77_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_77_17 = s_77_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_77_17).trans round_77_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_77_18 = s_77_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_77_18).trans round_77_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 10 = s_77_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_77_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_77_19 = s_77_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_77_19).trans round_77_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_77_20 = s_77_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_77_20).trans round_77_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) 11 = s_77_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_77_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_77_21 = s_77_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_77_21).trans round_77_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_77_22 = s_77_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_77_22).trans round_77_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell7719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell7719.canon3
  · exact PV_RunJoin_ValidatorCell7719.canon5
  · exact PV_RunJoin_ValidatorCell7719.canon7
  · exact PV_RunJoin_ValidatorCell7719.canon9
  · exact PV_RunJoin_ValidatorCell7719.canon11
  · exact PV_RunJoin_ValidatorCell7719.canon13
  · exact PV_RunJoin_ValidatorCell7719.canon15
  · exact PV_RunJoin_ValidatorCell7719.canon17
  · exact PV_RunJoin_ValidatorCell7719.canon19
  · exact PV_RunJoin_ValidatorCell7719.canon21
  · exact PV_RunJoin_ValidatorCell7719.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7719.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell7719.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell7719.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell7719.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell7719.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell7719.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell7719.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell7719.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell7719.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell7719.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell7719.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell7719.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell7719.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell7719.certificate.pre PV_RunJoin_BankCell7719.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell7719.certificate.pre PV_RunJoin_BankCell7719.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell7719.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell7720

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell7820
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell7819.certificate.pre) i +
    (liftA PV_RunJoin_BankCell7819.certificate.absorption) i else (liftA PV_RunJoin_BankCell7819.certificate.pre) i) = s_78_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 1 = s_78_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell7819.certificate.pre) (liftA PV_RunJoin_BankCell7819.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_78_1,round_78_2]
  exact round_78_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 2 = s_78_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_78_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_78_3 = s_78_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_78_3).trans round_78_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_78_4 = s_78_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_78_4).trans round_78_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 3 = s_78_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_78_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_78_5 = s_78_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_78_5).trans round_78_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_78_6 = s_78_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_78_6).trans round_78_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 4 = s_78_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_78_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_78_7 = s_78_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_78_7).trans round_78_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_78_8 = s_78_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_78_8).trans round_78_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 5 = s_78_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_78_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_78_9 = s_78_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_78_9).trans round_78_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_78_10 = s_78_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_78_10).trans round_78_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 6 = s_78_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_78_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_78_11 = s_78_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_78_11).trans round_78_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_78_12 = s_78_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_78_12).trans round_78_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 7 = s_78_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_78_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_78_13 = s_78_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_78_13).trans round_78_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_78_14 = s_78_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_78_14).trans round_78_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 8 = s_78_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_78_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_78_15 = s_78_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_78_15).trans round_78_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_78_16 = s_78_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_78_16).trans round_78_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 9 = s_78_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_78_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_78_17 = s_78_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_78_17).trans round_78_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_78_18 = s_78_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_78_18).trans round_78_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 10 = s_78_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_78_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_78_19 = s_78_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_78_19).trans round_78_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_78_20 = s_78_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_78_20).trans round_78_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) 11 = s_78_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_78_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_78_21 = s_78_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_78_21).trans round_78_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_78_22 = s_78_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_78_22).trans round_78_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell7819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell7819.canon3
  · exact PV_RunJoin_ValidatorCell7819.canon5
  · exact PV_RunJoin_ValidatorCell7819.canon7
  · exact PV_RunJoin_ValidatorCell7819.canon9
  · exact PV_RunJoin_ValidatorCell7819.canon11
  · exact PV_RunJoin_ValidatorCell7819.canon13
  · exact PV_RunJoin_ValidatorCell7819.canon15
  · exact PV_RunJoin_ValidatorCell7819.canon17
  · exact PV_RunJoin_ValidatorCell7819.canon19
  · exact PV_RunJoin_ValidatorCell7819.canon21
  · exact PV_RunJoin_ValidatorCell7819.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7819.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell7819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell7819.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell7819.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell7819.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell7819.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell7819.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell7819.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell7819.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell7819.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell7819.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell7819.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell7819.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell7819.certificate.pre PV_RunJoin_BankCell7819.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell7819.certificate.pre PV_RunJoin_BankCell7819.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell7819.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell7820

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell7920
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell7919.certificate.pre) i +
    (liftA PV_RunJoin_BankCell7919.certificate.absorption) i else (liftA PV_RunJoin_BankCell7919.certificate.pre) i) = s_79_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 1 = s_79_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell7919.certificate.pre) (liftA PV_RunJoin_BankCell7919.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_79_1,round_79_2]
  exact round_79_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 2 = s_79_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_79_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_79_3 = s_79_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_79_3).trans round_79_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_79_4 = s_79_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_79_4).trans round_79_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 3 = s_79_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_79_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_79_5 = s_79_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_79_5).trans round_79_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_79_6 = s_79_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_79_6).trans round_79_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 4 = s_79_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_79_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_79_7 = s_79_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_79_7).trans round_79_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_79_8 = s_79_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_79_8).trans round_79_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 5 = s_79_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_79_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_79_9 = s_79_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_79_9).trans round_79_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_79_10 = s_79_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_79_10).trans round_79_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 6 = s_79_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_79_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_79_11 = s_79_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_79_11).trans round_79_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_79_12 = s_79_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_79_12).trans round_79_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 7 = s_79_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_79_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_79_13 = s_79_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_79_13).trans round_79_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_79_14 = s_79_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_79_14).trans round_79_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 8 = s_79_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_79_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_79_15 = s_79_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_79_15).trans round_79_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_79_16 = s_79_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_79_16).trans round_79_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 9 = s_79_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_79_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_79_17 = s_79_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_79_17).trans round_79_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_79_18 = s_79_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_79_18).trans round_79_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 10 = s_79_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_79_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_79_19 = s_79_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_79_19).trans round_79_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_79_20 = s_79_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_79_20).trans round_79_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) 11 = s_79_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_79_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_79_21 = s_79_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_79_21).trans round_79_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_79_22 = s_79_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_79_22).trans round_79_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell7919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell7919.canon3
  · exact PV_RunJoin_ValidatorCell7919.canon5
  · exact PV_RunJoin_ValidatorCell7919.canon7
  · exact PV_RunJoin_ValidatorCell7919.canon9
  · exact PV_RunJoin_ValidatorCell7919.canon11
  · exact PV_RunJoin_ValidatorCell7919.canon13
  · exact PV_RunJoin_ValidatorCell7919.canon15
  · exact PV_RunJoin_ValidatorCell7919.canon17
  · exact PV_RunJoin_ValidatorCell7919.canon19
  · exact PV_RunJoin_ValidatorCell7919.canon21
  · exact PV_RunJoin_ValidatorCell7919.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell7919.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell7919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell7919.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell7919.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell7919.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell7919.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell7919.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell7919.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell7919.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell7919.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell7919.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell7919.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell7919.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell7919.certificate.pre PV_RunJoin_BankCell7919.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell7919.certificate.pre PV_RunJoin_BankCell7919.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell7919.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell7920

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell8020
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_OutputModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell8019.certificate.pre) i +
    (liftA PV_RunJoin_BankCell8019.certificate.absorption) i else (liftA PV_RunJoin_BankCell8019.certificate.pre) i) = s_80_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 1 = s_80_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell8019.certificate.pre) (liftA PV_RunJoin_BankCell8019.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_80_1,round_80_2]
  exact round_80_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 2 = s_80_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_80_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_80_3 = s_80_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_80_3).trans round_80_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_80_4 = s_80_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_80_4).trans round_80_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 3 = s_80_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_80_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_80_5 = s_80_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_80_5).trans round_80_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_80_6 = s_80_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_80_6).trans round_80_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 4 = s_80_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_80_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_80_7 = s_80_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_80_7).trans round_80_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_80_8 = s_80_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_80_8).trans round_80_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 5 = s_80_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_80_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_80_9 = s_80_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_80_9).trans round_80_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_80_10 = s_80_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_80_10).trans round_80_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 6 = s_80_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_80_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_80_11 = s_80_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_80_11).trans round_80_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_80_12 = s_80_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_80_12).trans round_80_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 7 = s_80_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_80_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_80_13 = s_80_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_80_13).trans round_80_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_80_14 = s_80_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_80_14).trans round_80_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 8 = s_80_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_80_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_80_15 = s_80_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_80_15).trans round_80_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_80_16 = s_80_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_80_16).trans round_80_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 9 = s_80_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_80_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_80_17 = s_80_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_80_17).trans round_80_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_80_18 = s_80_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_80_18).trans round_80_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 10 = s_80_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_80_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_80_19 = s_80_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_80_19).trans round_80_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_80_20 = s_80_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_80_20).trans round_80_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) 11 = s_80_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_80_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_80_21 = s_80_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_80_21).trans round_80_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_80_22 = s_80_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_80_22).trans round_80_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell8019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell8019.canon3
  · exact PV_RunJoin_ValidatorCell8019.canon5
  · exact PV_RunJoin_ValidatorCell8019.canon7
  · exact PV_RunJoin_ValidatorCell8019.canon9
  · exact PV_RunJoin_ValidatorCell8019.canon11
  · exact PV_RunJoin_ValidatorCell8019.canon13
  · exact PV_RunJoin_ValidatorCell8019.canon15
  · exact PV_RunJoin_ValidatorCell8019.canon17
  · exact PV_RunJoin_ValidatorCell8019.canon19
  · exact PV_RunJoin_ValidatorCell8019.canon21
  · exact PV_RunJoin_ValidatorCell8019.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell8019.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell8019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell8019.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell8019.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell8019.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell8019.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell8019.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell8019.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell8019.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell8019.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell8019.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell8019.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell8019.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell8019.certificate.pre PV_RunJoin_BankCell8019.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell8019.certificate.pre PV_RunJoin_BankCell8019.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell8019.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell8020
