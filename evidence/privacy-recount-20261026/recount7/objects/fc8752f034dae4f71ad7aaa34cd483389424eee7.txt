import R1Z.PV_RunJoin_CopyCertificate20
import R1Z.PV_RunJoin_BankCells1819
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell1820
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell1819.certificate.pre) i +
    (liftA PV_RunJoin_BankCell1819.certificate.absorption) i else (liftA PV_RunJoin_BankCell1819.certificate.pre) i) = s_18_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 1 = s_18_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell1819.certificate.pre) (liftA PV_RunJoin_BankCell1819.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_18_1,round_18_2]
  exact round_18_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 2 = s_18_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_18_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_18_3 = s_18_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_18_3).trans round_18_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_18_4 = s_18_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_18_4).trans round_18_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 3 = s_18_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_18_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_18_5 = s_18_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_18_5).trans round_18_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_18_6 = s_18_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_18_6).trans round_18_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 4 = s_18_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_18_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_18_7 = s_18_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_18_7).trans round_18_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_18_8 = s_18_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_18_8).trans round_18_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 5 = s_18_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_18_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_18_9 = s_18_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_18_9).trans round_18_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_18_10 = s_18_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_18_10).trans round_18_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 6 = s_18_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_18_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_18_11 = s_18_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_18_11).trans round_18_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_18_12 = s_18_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_18_12).trans round_18_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 7 = s_18_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_18_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_18_13 = s_18_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_18_13).trans round_18_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_18_14 = s_18_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_18_14).trans round_18_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 8 = s_18_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_18_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_18_15 = s_18_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_18_15).trans round_18_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_18_16 = s_18_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_18_16).trans round_18_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 9 = s_18_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_18_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_18_17 = s_18_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_18_17).trans round_18_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_18_18 = s_18_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_18_18).trans round_18_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 10 = s_18_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_18_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_18_19 = s_18_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_18_19).trans round_18_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_18_20 = s_18_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_18_20).trans round_18_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) 11 = s_18_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_18_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_18_21 = s_18_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_18_21).trans round_18_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_18_22 = s_18_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_18_22).trans round_18_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell1819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell1819.canon3
  · exact PV_RunJoin_ValidatorCell1819.canon5
  · exact PV_RunJoin_ValidatorCell1819.canon7
  · exact PV_RunJoin_ValidatorCell1819.canon9
  · exact PV_RunJoin_ValidatorCell1819.canon11
  · exact PV_RunJoin_ValidatorCell1819.canon13
  · exact PV_RunJoin_ValidatorCell1819.canon15
  · exact PV_RunJoin_ValidatorCell1819.canon17
  · exact PV_RunJoin_ValidatorCell1819.canon19
  · exact PV_RunJoin_ValidatorCell1819.canon21
  · exact PV_RunJoin_ValidatorCell1819.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1819.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell1819.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell1819.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell1819.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell1819.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell1819.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell1819.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell1819.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell1819.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell1819.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell1819.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell1819.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell1819.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell1819.certificate.pre PV_RunJoin_BankCell1819.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell1819.certificate.pre PV_RunJoin_BankCell1819.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell1819.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell1820

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell1920
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell1919.certificate.pre) i +
    (liftA PV_RunJoin_BankCell1919.certificate.absorption) i else (liftA PV_RunJoin_BankCell1919.certificate.pre) i) = s_19_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 1 = s_19_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell1919.certificate.pre) (liftA PV_RunJoin_BankCell1919.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_19_1,round_19_2]
  exact round_19_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 2 = s_19_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_19_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_19_3 = s_19_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_19_3).trans round_19_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_19_4 = s_19_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_19_4).trans round_19_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 3 = s_19_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_19_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_19_5 = s_19_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_19_5).trans round_19_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_19_6 = s_19_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_19_6).trans round_19_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 4 = s_19_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_19_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_19_7 = s_19_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_19_7).trans round_19_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_19_8 = s_19_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_19_8).trans round_19_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 5 = s_19_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_19_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_19_9 = s_19_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_19_9).trans round_19_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_19_10 = s_19_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_19_10).trans round_19_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 6 = s_19_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_19_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_19_11 = s_19_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_19_11).trans round_19_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_19_12 = s_19_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_19_12).trans round_19_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 7 = s_19_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_19_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_19_13 = s_19_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_19_13).trans round_19_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_19_14 = s_19_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_19_14).trans round_19_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 8 = s_19_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_19_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_19_15 = s_19_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_19_15).trans round_19_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_19_16 = s_19_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_19_16).trans round_19_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 9 = s_19_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_19_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_19_17 = s_19_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_19_17).trans round_19_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_19_18 = s_19_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_19_18).trans round_19_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 10 = s_19_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_19_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_19_19 = s_19_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_19_19).trans round_19_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_19_20 = s_19_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_19_20).trans round_19_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) 11 = s_19_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_19_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_19_21 = s_19_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_19_21).trans round_19_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_19_22 = s_19_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_19_22).trans round_19_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell1919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell1919.canon3
  · exact PV_RunJoin_ValidatorCell1919.canon5
  · exact PV_RunJoin_ValidatorCell1919.canon7
  · exact PV_RunJoin_ValidatorCell1919.canon9
  · exact PV_RunJoin_ValidatorCell1919.canon11
  · exact PV_RunJoin_ValidatorCell1919.canon13
  · exact PV_RunJoin_ValidatorCell1919.canon15
  · exact PV_RunJoin_ValidatorCell1919.canon17
  · exact PV_RunJoin_ValidatorCell1919.canon19
  · exact PV_RunJoin_ValidatorCell1919.canon21
  · exact PV_RunJoin_ValidatorCell1919.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell1919.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell1919.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell1919.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell1919.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell1919.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell1919.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell1919.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell1919.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell1919.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell1919.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell1919.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell1919.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell1919.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell1919.certificate.pre PV_RunJoin_BankCell1919.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell1919.certificate.pre PV_RunJoin_BankCell1919.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell1919.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell1920

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell2020
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell2019.certificate.pre) i +
    (liftA PV_RunJoin_BankCell2019.certificate.absorption) i else (liftA PV_RunJoin_BankCell2019.certificate.pre) i) = s_20_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 1 = s_20_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell2019.certificate.pre) (liftA PV_RunJoin_BankCell2019.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_20_1,round_20_2]
  exact round_20_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 2 = s_20_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_20_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_20_3 = s_20_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_20_3).trans round_20_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_20_4 = s_20_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_20_4).trans round_20_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 3 = s_20_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_20_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_20_5 = s_20_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_20_5).trans round_20_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_20_6 = s_20_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_20_6).trans round_20_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 4 = s_20_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_20_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_20_7 = s_20_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_20_7).trans round_20_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_20_8 = s_20_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_20_8).trans round_20_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 5 = s_20_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_20_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_20_9 = s_20_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_20_9).trans round_20_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_20_10 = s_20_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_20_10).trans round_20_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 6 = s_20_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_20_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_20_11 = s_20_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_20_11).trans round_20_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_20_12 = s_20_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_20_12).trans round_20_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 7 = s_20_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_20_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_20_13 = s_20_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_20_13).trans round_20_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_20_14 = s_20_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_20_14).trans round_20_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 8 = s_20_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_20_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_20_15 = s_20_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_20_15).trans round_20_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_20_16 = s_20_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_20_16).trans round_20_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 9 = s_20_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_20_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_20_17 = s_20_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_20_17).trans round_20_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_20_18 = s_20_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_20_18).trans round_20_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 10 = s_20_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_20_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_20_19 = s_20_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_20_19).trans round_20_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_20_20 = s_20_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_20_20).trans round_20_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) 11 = s_20_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_20_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_20_21 = s_20_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_20_21).trans round_20_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_20_22 = s_20_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_20_22).trans round_20_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell2019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell2019.canon3
  · exact PV_RunJoin_ValidatorCell2019.canon5
  · exact PV_RunJoin_ValidatorCell2019.canon7
  · exact PV_RunJoin_ValidatorCell2019.canon9
  · exact PV_RunJoin_ValidatorCell2019.canon11
  · exact PV_RunJoin_ValidatorCell2019.canon13
  · exact PV_RunJoin_ValidatorCell2019.canon15
  · exact PV_RunJoin_ValidatorCell2019.canon17
  · exact PV_RunJoin_ValidatorCell2019.canon19
  · exact PV_RunJoin_ValidatorCell2019.canon21
  · exact PV_RunJoin_ValidatorCell2019.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2019.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell2019.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell2019.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell2019.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell2019.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell2019.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell2019.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell2019.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell2019.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell2019.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell2019.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell2019.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell2019.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell2019.certificate.pre PV_RunJoin_BankCell2019.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell2019.certificate.pre PV_RunJoin_BankCell2019.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell2019.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell2020

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell2120
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell2119.certificate.pre) i +
    (liftA PV_RunJoin_BankCell2119.certificate.absorption) i else (liftA PV_RunJoin_BankCell2119.certificate.pre) i) = s_21_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 1 = s_21_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell2119.certificate.pre) (liftA PV_RunJoin_BankCell2119.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_21_1,round_21_2]
  exact round_21_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 2 = s_21_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_21_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_21_3 = s_21_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_21_3).trans round_21_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_21_4 = s_21_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_21_4).trans round_21_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 3 = s_21_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_21_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_21_5 = s_21_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_21_5).trans round_21_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_21_6 = s_21_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_21_6).trans round_21_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 4 = s_21_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_21_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_21_7 = s_21_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_21_7).trans round_21_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_21_8 = s_21_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_21_8).trans round_21_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 5 = s_21_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_21_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_21_9 = s_21_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_21_9).trans round_21_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_21_10 = s_21_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_21_10).trans round_21_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 6 = s_21_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_21_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_21_11 = s_21_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_21_11).trans round_21_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_21_12 = s_21_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_21_12).trans round_21_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 7 = s_21_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_21_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_21_13 = s_21_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_21_13).trans round_21_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_21_14 = s_21_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_21_14).trans round_21_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 8 = s_21_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_21_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_21_15 = s_21_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_21_15).trans round_21_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_21_16 = s_21_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_21_16).trans round_21_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 9 = s_21_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_21_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_21_17 = s_21_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_21_17).trans round_21_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_21_18 = s_21_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_21_18).trans round_21_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 10 = s_21_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_21_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_21_19 = s_21_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_21_19).trans round_21_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_21_20 = s_21_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_21_20).trans round_21_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) 11 = s_21_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_21_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_21_21 = s_21_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_21_21).trans round_21_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_21_22 = s_21_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_21_22).trans round_21_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell2119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell2119.canon3
  · exact PV_RunJoin_ValidatorCell2119.canon5
  · exact PV_RunJoin_ValidatorCell2119.canon7
  · exact PV_RunJoin_ValidatorCell2119.canon9
  · exact PV_RunJoin_ValidatorCell2119.canon11
  · exact PV_RunJoin_ValidatorCell2119.canon13
  · exact PV_RunJoin_ValidatorCell2119.canon15
  · exact PV_RunJoin_ValidatorCell2119.canon17
  · exact PV_RunJoin_ValidatorCell2119.canon19
  · exact PV_RunJoin_ValidatorCell2119.canon21
  · exact PV_RunJoin_ValidatorCell2119.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2119.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell2119.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell2119.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell2119.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell2119.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell2119.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell2119.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell2119.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell2119.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell2119.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell2119.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell2119.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell2119.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell2119.certificate.pre PV_RunJoin_BankCell2119.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell2119.certificate.pre PV_RunJoin_BankCell2119.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell2119.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell2120

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell2220
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell2219.certificate.pre) i +
    (liftA PV_RunJoin_BankCell2219.certificate.absorption) i else (liftA PV_RunJoin_BankCell2219.certificate.pre) i) = s_22_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 1 = s_22_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell2219.certificate.pre) (liftA PV_RunJoin_BankCell2219.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_22_1,round_22_2]
  exact round_22_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 2 = s_22_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_22_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_22_3 = s_22_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_22_3).trans round_22_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_22_4 = s_22_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_22_4).trans round_22_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 3 = s_22_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_22_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_22_5 = s_22_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_22_5).trans round_22_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_22_6 = s_22_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_22_6).trans round_22_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 4 = s_22_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_22_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_22_7 = s_22_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_22_7).trans round_22_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_22_8 = s_22_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_22_8).trans round_22_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 5 = s_22_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_22_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_22_9 = s_22_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_22_9).trans round_22_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_22_10 = s_22_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_22_10).trans round_22_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 6 = s_22_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_22_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_22_11 = s_22_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_22_11).trans round_22_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_22_12 = s_22_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_22_12).trans round_22_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 7 = s_22_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_22_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_22_13 = s_22_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_22_13).trans round_22_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_22_14 = s_22_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_22_14).trans round_22_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 8 = s_22_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_22_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_22_15 = s_22_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_22_15).trans round_22_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_22_16 = s_22_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_22_16).trans round_22_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 9 = s_22_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_22_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_22_17 = s_22_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_22_17).trans round_22_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_22_18 = s_22_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_22_18).trans round_22_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 10 = s_22_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_22_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_22_19 = s_22_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_22_19).trans round_22_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_22_20 = s_22_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_22_20).trans round_22_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) 11 = s_22_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_22_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_22_21 = s_22_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_22_21).trans round_22_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_22_22 = s_22_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_22_22).trans round_22_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell2219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell2219.canon3
  · exact PV_RunJoin_ValidatorCell2219.canon5
  · exact PV_RunJoin_ValidatorCell2219.canon7
  · exact PV_RunJoin_ValidatorCell2219.canon9
  · exact PV_RunJoin_ValidatorCell2219.canon11
  · exact PV_RunJoin_ValidatorCell2219.canon13
  · exact PV_RunJoin_ValidatorCell2219.canon15
  · exact PV_RunJoin_ValidatorCell2219.canon17
  · exact PV_RunJoin_ValidatorCell2219.canon19
  · exact PV_RunJoin_ValidatorCell2219.canon21
  · exact PV_RunJoin_ValidatorCell2219.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2219.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell2219.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell2219.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell2219.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell2219.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell2219.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell2219.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell2219.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell2219.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell2219.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell2219.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell2219.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell2219.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell2219.certificate.pre PV_RunJoin_BankCell2219.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell2219.certificate.pre PV_RunJoin_BankCell2219.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell2219.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell2220

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell2320
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell2319.certificate.pre) i +
    (liftA PV_RunJoin_BankCell2319.certificate.absorption) i else (liftA PV_RunJoin_BankCell2319.certificate.pre) i) = s_23_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 1 = s_23_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell2319.certificate.pre) (liftA PV_RunJoin_BankCell2319.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_23_1,round_23_2]
  exact round_23_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 2 = s_23_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_23_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_23_3 = s_23_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_23_3).trans round_23_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_23_4 = s_23_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_23_4).trans round_23_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 3 = s_23_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_23_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_23_5 = s_23_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_23_5).trans round_23_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_23_6 = s_23_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_23_6).trans round_23_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 4 = s_23_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_23_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_23_7 = s_23_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_23_7).trans round_23_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_23_8 = s_23_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_23_8).trans round_23_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 5 = s_23_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_23_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_23_9 = s_23_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_23_9).trans round_23_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_23_10 = s_23_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_23_10).trans round_23_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 6 = s_23_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_23_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_23_11 = s_23_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_23_11).trans round_23_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_23_12 = s_23_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_23_12).trans round_23_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 7 = s_23_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_23_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_23_13 = s_23_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_23_13).trans round_23_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_23_14 = s_23_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_23_14).trans round_23_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 8 = s_23_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_23_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_23_15 = s_23_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_23_15).trans round_23_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_23_16 = s_23_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_23_16).trans round_23_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 9 = s_23_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_23_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_23_17 = s_23_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_23_17).trans round_23_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_23_18 = s_23_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_23_18).trans round_23_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 10 = s_23_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_23_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_23_19 = s_23_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_23_19).trans round_23_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_23_20 = s_23_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_23_20).trans round_23_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) 11 = s_23_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_23_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_23_21 = s_23_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_23_21).trans round_23_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_23_22 = s_23_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_23_22).trans round_23_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell2319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell2319.canon3
  · exact PV_RunJoin_ValidatorCell2319.canon5
  · exact PV_RunJoin_ValidatorCell2319.canon7
  · exact PV_RunJoin_ValidatorCell2319.canon9
  · exact PV_RunJoin_ValidatorCell2319.canon11
  · exact PV_RunJoin_ValidatorCell2319.canon13
  · exact PV_RunJoin_ValidatorCell2319.canon15
  · exact PV_RunJoin_ValidatorCell2319.canon17
  · exact PV_RunJoin_ValidatorCell2319.canon19
  · exact PV_RunJoin_ValidatorCell2319.canon21
  · exact PV_RunJoin_ValidatorCell2319.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2319.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell2319.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell2319.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell2319.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell2319.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell2319.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell2319.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell2319.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell2319.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell2319.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell2319.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell2319.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell2319.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell2319.certificate.pre PV_RunJoin_BankCell2319.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell2319.certificate.pre PV_RunJoin_BankCell2319.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell2319.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell2320

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell2420
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell2419.certificate.pre) i +
    (liftA PV_RunJoin_BankCell2419.certificate.absorption) i else (liftA PV_RunJoin_BankCell2419.certificate.pre) i) = s_24_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 1 = s_24_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell2419.certificate.pre) (liftA PV_RunJoin_BankCell2419.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_24_1,round_24_2]
  exact round_24_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 2 = s_24_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_24_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_24_3 = s_24_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_24_3).trans round_24_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_24_4 = s_24_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_24_4).trans round_24_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 3 = s_24_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_24_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_24_5 = s_24_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_24_5).trans round_24_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_24_6 = s_24_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_24_6).trans round_24_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 4 = s_24_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_24_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_24_7 = s_24_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_24_7).trans round_24_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_24_8 = s_24_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_24_8).trans round_24_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 5 = s_24_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_24_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_24_9 = s_24_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_24_9).trans round_24_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_24_10 = s_24_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_24_10).trans round_24_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 6 = s_24_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_24_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_24_11 = s_24_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_24_11).trans round_24_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_24_12 = s_24_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_24_12).trans round_24_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 7 = s_24_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_24_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_24_13 = s_24_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_24_13).trans round_24_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_24_14 = s_24_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_24_14).trans round_24_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 8 = s_24_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_24_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_24_15 = s_24_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_24_15).trans round_24_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_24_16 = s_24_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_24_16).trans round_24_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 9 = s_24_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_24_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_24_17 = s_24_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_24_17).trans round_24_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_24_18 = s_24_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_24_18).trans round_24_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 10 = s_24_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_24_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_24_19 = s_24_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_24_19).trans round_24_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_24_20 = s_24_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_24_20).trans round_24_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) 11 = s_24_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_24_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_24_21 = s_24_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_24_21).trans round_24_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_24_22 = s_24_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_24_22).trans round_24_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell2419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell2419.canon3
  · exact PV_RunJoin_ValidatorCell2419.canon5
  · exact PV_RunJoin_ValidatorCell2419.canon7
  · exact PV_RunJoin_ValidatorCell2419.canon9
  · exact PV_RunJoin_ValidatorCell2419.canon11
  · exact PV_RunJoin_ValidatorCell2419.canon13
  · exact PV_RunJoin_ValidatorCell2419.canon15
  · exact PV_RunJoin_ValidatorCell2419.canon17
  · exact PV_RunJoin_ValidatorCell2419.canon19
  · exact PV_RunJoin_ValidatorCell2419.canon21
  · exact PV_RunJoin_ValidatorCell2419.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2419.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell2419.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell2419.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell2419.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell2419.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell2419.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell2419.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell2419.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell2419.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell2419.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell2419.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell2419.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell2419.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell2419.certificate.pre PV_RunJoin_BankCell2419.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell2419.certificate.pre PV_RunJoin_BankCell2419.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell2419.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell2420

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell2520
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell2519.certificate.pre) i +
    (liftA PV_RunJoin_BankCell2519.certificate.absorption) i else (liftA PV_RunJoin_BankCell2519.certificate.pre) i) = s_25_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 1 = s_25_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell2519.certificate.pre) (liftA PV_RunJoin_BankCell2519.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_25_1,round_25_2]
  exact round_25_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 2 = s_25_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_25_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_25_3 = s_25_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_25_3).trans round_25_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_25_4 = s_25_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_25_4).trans round_25_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 3 = s_25_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_25_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_25_5 = s_25_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_25_5).trans round_25_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_25_6 = s_25_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_25_6).trans round_25_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 4 = s_25_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_25_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_25_7 = s_25_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_25_7).trans round_25_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_25_8 = s_25_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_25_8).trans round_25_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 5 = s_25_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_25_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_25_9 = s_25_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_25_9).trans round_25_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_25_10 = s_25_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_25_10).trans round_25_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 6 = s_25_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_25_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_25_11 = s_25_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_25_11).trans round_25_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_25_12 = s_25_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_25_12).trans round_25_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 7 = s_25_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_25_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_25_13 = s_25_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_25_13).trans round_25_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_25_14 = s_25_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_25_14).trans round_25_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 8 = s_25_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_25_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_25_15 = s_25_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_25_15).trans round_25_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_25_16 = s_25_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_25_16).trans round_25_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 9 = s_25_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_25_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_25_17 = s_25_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_25_17).trans round_25_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_25_18 = s_25_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_25_18).trans round_25_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 10 = s_25_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_25_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_25_19 = s_25_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_25_19).trans round_25_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_25_20 = s_25_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_25_20).trans round_25_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) 11 = s_25_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_25_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_25_21 = s_25_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_25_21).trans round_25_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_25_22 = s_25_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_25_22).trans round_25_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell2519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell2519.canon3
  · exact PV_RunJoin_ValidatorCell2519.canon5
  · exact PV_RunJoin_ValidatorCell2519.canon7
  · exact PV_RunJoin_ValidatorCell2519.canon9
  · exact PV_RunJoin_ValidatorCell2519.canon11
  · exact PV_RunJoin_ValidatorCell2519.canon13
  · exact PV_RunJoin_ValidatorCell2519.canon15
  · exact PV_RunJoin_ValidatorCell2519.canon17
  · exact PV_RunJoin_ValidatorCell2519.canon19
  · exact PV_RunJoin_ValidatorCell2519.canon21
  · exact PV_RunJoin_ValidatorCell2519.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2519.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell2519.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell2519.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell2519.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell2519.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell2519.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell2519.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell2519.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell2519.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell2519.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell2519.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell2519.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell2519.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell2519.certificate.pre PV_RunJoin_BankCell2519.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell2519.certificate.pre PV_RunJoin_BankCell2519.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell2519.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell2520

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCell2620
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_RunJoin_PathModel16

theorem combined : (fun i => if i.val < 8 then (liftA (K := M) PV_RunJoin_BankCell2619.certificate.pre) i +
    (liftA PV_RunJoin_BankCell2619.certificate.absorption) i else (liftA PV_RunJoin_BankCell2619.certificate.pre) i) = s_26_0 := by
  funext i
  fin_cases i <;> with_unfolding_all rfl
#print axioms combined
theorem model1 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 1 = s_26_3 := by
  rw [iter_succ _ 0 (by decide)]
  rw [iter_zero,trans_zero]
  change R0P.poseidonLeadingPair (liftA PV_RunJoin_BankCell2619.certificate.pre) (liftA PV_RunJoin_BankCell2619.certificate.absorption) = _
  rw [R0P.poseidonLeadingPair,combined,round_26_1,round_26_2]
  exact round_26_3
#print axioms model1
theorem model2 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 2 = s_26_5 := by
  rw [iter_succ _ 1 (by decide)]
  rw [model1,trans_succ 1 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨3,by decide⟩
    (R0P.poseidonApplyRound ⟨2,by decide⟩ s_26_3) = _
  have step2 : R0P.poseidonApplyRound ⟨2,by decide⟩ s_26_3 = s_26_4 :=
    (ar_init ⟨2,by decide⟩ (by decide) s_26_3).trans round_26_4
  have step3 : R0P.poseidonApplyRound ⟨3,by decide⟩ s_26_4 = s_26_5 :=
    (ar_init ⟨3,by decide⟩ (by decide) s_26_4).trans round_26_5
  exact (congrArg (R0P.poseidonApplyRound ⟨3,by decide⟩) step2).trans step3
#print axioms model2
theorem model3 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 3 = s_26_7 := by
  rw [iter_succ _ 2 (by decide)]
  rw [model2,trans_succ 2 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨5,by decide⟩
    (R0P.poseidonApplyRound ⟨4,by decide⟩ s_26_5) = _
  have step4 : R0P.poseidonApplyRound ⟨4,by decide⟩ s_26_5 = s_26_6 :=
    (ar_int ⟨4,by decide⟩ (by decide) (by decide) s_26_5).trans round_26_6
  have step5 : R0P.poseidonApplyRound ⟨5,by decide⟩ s_26_6 = s_26_7 :=
    (ar_int ⟨5,by decide⟩ (by decide) (by decide) s_26_6).trans round_26_7
  exact (congrArg (R0P.poseidonApplyRound ⟨5,by decide⟩) step4).trans step5
#print axioms model3
theorem model4 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 4 = s_26_9 := by
  rw [iter_succ _ 3 (by decide)]
  rw [model3,trans_succ 3 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨7,by decide⟩
    (R0P.poseidonApplyRound ⟨6,by decide⟩ s_26_7) = _
  have step6 : R0P.poseidonApplyRound ⟨6,by decide⟩ s_26_7 = s_26_8 :=
    (ar_int ⟨6,by decide⟩ (by decide) (by decide) s_26_7).trans round_26_8
  have step7 : R0P.poseidonApplyRound ⟨7,by decide⟩ s_26_8 = s_26_9 :=
    (ar_int ⟨7,by decide⟩ (by decide) (by decide) s_26_8).trans round_26_9
  exact (congrArg (R0P.poseidonApplyRound ⟨7,by decide⟩) step6).trans step7
#print axioms model4
theorem model5 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 5 = s_26_11 := by
  rw [iter_succ _ 4 (by decide)]
  rw [model4,trans_succ 4 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨9,by decide⟩
    (R0P.poseidonApplyRound ⟨8,by decide⟩ s_26_9) = _
  have step8 : R0P.poseidonApplyRound ⟨8,by decide⟩ s_26_9 = s_26_10 :=
    (ar_int ⟨8,by decide⟩ (by decide) (by decide) s_26_9).trans round_26_10
  have step9 : R0P.poseidonApplyRound ⟨9,by decide⟩ s_26_10 = s_26_11 :=
    (ar_int ⟨9,by decide⟩ (by decide) (by decide) s_26_10).trans round_26_11
  exact (congrArg (R0P.poseidonApplyRound ⟨9,by decide⟩) step8).trans step9
#print axioms model5
theorem model6 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 6 = s_26_13 := by
  rw [iter_succ _ 5 (by decide)]
  rw [model5,trans_succ 5 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨11,by decide⟩
    (R0P.poseidonApplyRound ⟨10,by decide⟩ s_26_11) = _
  have step10 : R0P.poseidonApplyRound ⟨10,by decide⟩ s_26_11 = s_26_12 :=
    (ar_int ⟨10,by decide⟩ (by decide) (by decide) s_26_11).trans round_26_12
  have step11 : R0P.poseidonApplyRound ⟨11,by decide⟩ s_26_12 = s_26_13 :=
    (ar_int ⟨11,by decide⟩ (by decide) (by decide) s_26_12).trans round_26_13
  exact (congrArg (R0P.poseidonApplyRound ⟨11,by decide⟩) step10).trans step11
#print axioms model6
theorem model7 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 7 = s_26_15 := by
  rw [iter_succ _ 6 (by decide)]
  rw [model6,trans_succ 6 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨13,by decide⟩
    (R0P.poseidonApplyRound ⟨12,by decide⟩ s_26_13) = _
  have step12 : R0P.poseidonApplyRound ⟨12,by decide⟩ s_26_13 = s_26_14 :=
    (ar_int ⟨12,by decide⟩ (by decide) (by decide) s_26_13).trans round_26_14
  have step13 : R0P.poseidonApplyRound ⟨13,by decide⟩ s_26_14 = s_26_15 :=
    (ar_int ⟨13,by decide⟩ (by decide) (by decide) s_26_14).trans round_26_15
  exact (congrArg (R0P.poseidonApplyRound ⟨13,by decide⟩) step12).trans step13
#print axioms model7
theorem model8 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 8 = s_26_17 := by
  rw [iter_succ _ 7 (by decide)]
  rw [model7,trans_succ 7 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨15,by decide⟩
    (R0P.poseidonApplyRound ⟨14,by decide⟩ s_26_15) = _
  have step14 : R0P.poseidonApplyRound ⟨14,by decide⟩ s_26_15 = s_26_16 :=
    (ar_int ⟨14,by decide⟩ (by decide) (by decide) s_26_15).trans round_26_16
  have step15 : R0P.poseidonApplyRound ⟨15,by decide⟩ s_26_16 = s_26_17 :=
    (ar_int ⟨15,by decide⟩ (by decide) (by decide) s_26_16).trans round_26_17
  exact (congrArg (R0P.poseidonApplyRound ⟨15,by decide⟩) step14).trans step15
#print axioms model8
theorem model9 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 9 = s_26_19 := by
  rw [iter_succ _ 8 (by decide)]
  rw [model8,trans_succ 8 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨17,by decide⟩
    (R0P.poseidonApplyRound ⟨16,by decide⟩ s_26_17) = _
  have step16 : R0P.poseidonApplyRound ⟨16,by decide⟩ s_26_17 = s_26_18 :=
    (ar_int ⟨16,by decide⟩ (by decide) (by decide) s_26_17).trans round_26_18
  have step17 : R0P.poseidonApplyRound ⟨17,by decide⟩ s_26_18 = s_26_19 :=
    (ar_int ⟨17,by decide⟩ (by decide) (by decide) s_26_18).trans round_26_19
  exact (congrArg (R0P.poseidonApplyRound ⟨17,by decide⟩) step16).trans step17
#print axioms model9
theorem model10 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 10 = s_26_21 := by
  rw [iter_succ _ 9 (by decide)]
  rw [model9,trans_succ 9 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨19,by decide⟩
    (R0P.poseidonApplyRound ⟨18,by decide⟩ s_26_19) = _
  have step18 : R0P.poseidonApplyRound ⟨18,by decide⟩ s_26_19 = s_26_20 :=
    (ar_fin ⟨18,by decide⟩ (by decide) (by decide) s_26_19).trans round_26_20
  have step19 : R0P.poseidonApplyRound ⟨19,by decide⟩ s_26_20 = s_26_21 :=
    (ar_fin ⟨19,by decide⟩ (by decide) (by decide) s_26_20).trans round_26_21
  exact (congrArg (R0P.poseidonApplyRound ⟨19,by decide⟩) step18).trans step19
#print axioms model10
theorem model11 : R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) 11 = s_26_23 := by
  rw [iter_succ _ 10 (by decide)]
  rw [model10,trans_succ 10 (by decide) (by decide)]
  change R0P.poseidonApplyRound ⟨21,by decide⟩
    (R0P.poseidonApplyRound ⟨20,by decide⟩ s_26_21) = _
  have step20 : R0P.poseidonApplyRound ⟨20,by decide⟩ s_26_21 = s_26_22 :=
    (ar_fin ⟨20,by decide⟩ (by decide) (by decide) s_26_21).trans round_26_22
  have step21 : R0P.poseidonApplyRound ⟨21,by decide⟩ s_26_22 = s_26_23 :=
    (ar_fin ⟨21,by decide⟩ (by decide) (by decide) s_26_22).trans round_26_23
  exact (congrArg (R0P.poseidonApplyRound ⟨21,by decide⟩) step20).trans step21
#print axioms model11
theorem canon : ∀ n, n < 11 → Canonical (PV_RunJoin_BankCell2619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact PV_RunJoin_ValidatorCell2619.canon3
  · exact PV_RunJoin_ValidatorCell2619.canon5
  · exact PV_RunJoin_ValidatorCell2619.canon7
  · exact PV_RunJoin_ValidatorCell2619.canon9
  · exact PV_RunJoin_ValidatorCell2619.canon11
  · exact PV_RunJoin_ValidatorCell2619.canon13
  · exact PV_RunJoin_ValidatorCell2619.canon15
  · exact PV_RunJoin_ValidatorCell2619.canon17
  · exact PV_RunJoin_ValidatorCell2619.canon19
  · exact PV_RunJoin_ValidatorCell2619.canon21
  · exact PV_RunJoin_ValidatorCell2619.canon23
#print axioms canon
theorem models : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model PV_RunJoin_BankCell2619.certificate) (n+1) =
    liftA (PV_RunJoin_BankCell2619.certificate.states (n+1)) := by
  intro n hn
  interval_cases n
  · exact model1.trans PV_RunJoin_ValidatorCell2619.lift3.symm
  · exact model2.trans PV_RunJoin_ValidatorCell2619.lift5.symm
  · exact model3.trans PV_RunJoin_ValidatorCell2619.lift7.symm
  · exact model4.trans PV_RunJoin_ValidatorCell2619.lift9.symm
  · exact model5.trans PV_RunJoin_ValidatorCell2619.lift11.symm
  · exact model6.trans PV_RunJoin_ValidatorCell2619.lift13.symm
  · exact model7.trans PV_RunJoin_ValidatorCell2619.lift15.symm
  · exact model8.trans PV_RunJoin_ValidatorCell2619.lift17.symm
  · exact model9.trans PV_RunJoin_ValidatorCell2619.lift19.symm
  · exact model10.trans PV_RunJoin_ValidatorCell2619.lift21.symm
  · exact model11.trans PV_RunJoin_ValidatorCell2619.lift23.symm
#print axioms models
theorem writer : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds PV_RunJoin_BankCell2619.certificate.pre PV_RunJoin_BankCell2619.certificate.absorption
      R0BlockCopies.write_block PV_RunJoin_BankCell2619.certificate.pre PV_RunJoin_BankCell2619.certificate.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (PV_RunJoin_BankCell2619.certificate.row row).val[lane]! :=
  PV_RunJoin_CopyCertificate20.writer _ canon models
#print axioms writer
end R1Z.PV_RunJoin_CopyCell2620
