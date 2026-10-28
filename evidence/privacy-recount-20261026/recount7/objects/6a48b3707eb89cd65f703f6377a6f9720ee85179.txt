import R1Z.PV_RunJoin_AbsorbShape20
import R1Z.PV_RunJoin_CopyCell0020
import R1Z.PV_RunJoin_CopyGroup0020
import R1Z.PV_RunJoin_CopyGroup2720
import R1Z.PV_RunJoin_CopyGroup3620
import R1Z.PV_RunJoin_SourceSponge0020
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceSponge3020.transfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell3319.certificate
theorem init : initNote = ok c.pre := by with_unfolding_all rfl
#print axioms init
theorem pre : spongePre (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 30 = ok c.pre := init
#print axioms pre
theorem absorb : R0BlockCopies.sponge_absorb ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).schunk 30) ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).sclen 30) = ok c.absorption := by
  apply PV_RunJoin_AbsorbShape20.sponge
  intro lane hl
  interval_cases lane <;> with_unfolding_all rfl
#print axioms absorb
theorem step : spongeStep c.pre ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).schunk 30) ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).sclen 30) = ok (c.states 11) :=
  PV_RunJoin_CertificateExecution20.sponge c PV_RunJoin_CopyCell3320.canon PV_RunJoin_CopyCell3320.models _ _ absorb
#print axioms step

theorem digest : spongeDigestR c.pre ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).schunk 30) ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).sclen 30) = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  rw [spongeDigestR,absorb]
  simp only [bind_tc_ok]
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell3320.canon PV_RunJoin_CopyCell3320.models
#print axioms digest
theorem chain : ∃ block, RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 30 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.sponge transferWitness transferPublic 30 c
    (by decide) (by decide) pre absorb PV_RunJoin_CopyCell3320.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 →
      (pt.blocks.val[30]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 30 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceSponge3020.transfer
namespace R1Z.PV_RunJoin_SourceSponge3020.withdrawal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell3619.certificate
theorem init : initNote = ok c.pre := by with_unfolding_all rfl
#print axioms init
theorem pre : spongePre (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 30 = ok c.pre := init
#print axioms pre
theorem absorb : R0BlockCopies.sponge_absorb ((rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)).schunk 30) ((rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)).sclen 30) = ok c.absorption := by
  apply PV_RunJoin_AbsorbShape20.sponge
  intro lane hl
  interval_cases lane <;> with_unfolding_all rfl
#print axioms absorb
theorem step : spongeStep c.pre ((rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)).schunk 30) ((rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)).sclen 30) = ok (c.states 11) :=
  PV_RunJoin_CertificateExecution20.sponge c PV_RunJoin_CopyCell3620.canon PV_RunJoin_CopyCell3620.models _ _ absorb
#print axioms step

theorem digest : spongeDigestR c.pre ((rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)).schunk 30) ((rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)).sclen 30) = ok (R0Z.WriterRefine.digest8 (c.states 11)) := by
  rw [spongeDigestR,absorb]
  simp only [bind_tc_ok]
  exact PV_RunJoin_CertificateExecution20.digest c PV_RunJoin_CopyCell3620.canon PV_RunJoin_CopyCell3620.models
#print axioms digest
theorem chain : ∃ block, RustWriterChain (wordPublic withdrawalPublic).variant (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) 30 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.sponge withdrawalWitness withdrawalPublic 30 c
    (by decide) (by decide) pre absorb PV_RunJoin_CopyCell3620.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 →
      (pt.blocks.val[30]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ 30 (by decide) c chain pt hp
#print axioms rows
end R1Z.PV_RunJoin_SourceSponge3020.withdrawal
