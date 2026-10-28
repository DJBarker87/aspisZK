import R1Z.PV_RunJoin_CopyCell0020
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceBlock0020
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankCell0019.certificate

theorem transfer_pre : spongePre (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 0 = ok c.pre := by
  with_unfolding_all rfl
#print axioms transfer_pre

theorem transfer_absorb : R0BlockCopies.sponge_absorb
    ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).schunk 0)
    ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).sclen 0) = ok c.absorption := by
  obtain ⟨ab,ha,hv⟩ := sponge_absorb_spec
    ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).schunk 0)
    ((rustChunks (wordWitness transferWitness) (wordPublic transferPublic)).sclen 0)
  have he : ab = c.absorption := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    rw [hv]
    have hj16 : j < 16 := by simpa using hj
    interval_cases j <;> with_unfolding_all rfl
  exact ha.trans (congrArg Result.ok he)
#print axioms transfer_absorb

theorem transfer_chain : ∃ block,
    RustWriterChain (wordPublic transferPublic).variant (rustChunks (wordWitness transferWitness) (wordPublic transferPublic)) 0 = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  obtain ⟨block,hb,hv⟩ := PV_RunJoin_CopyCell0020.writer
  refine ⟨block,?_,hv⟩
  rw [RustWriterChain,if_neg (show ¬ NodeKind 0 by decide),if_neg (show ¬ ZeroKind (wordPublic transferPublic).variant 0 by decide)]
  rw [transfer_pre]
  simp only [bind_tc_ok]
  rw [transfer_absorb]
  simp only [bind_tc_ok]
  exact hb
#print axioms transfer_chain

theorem transfer (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 →
      (pt.blocks.val[0]!).val[row*16+lane]! = (c.row row).val[lane]! := by
  obtain ⟨block,hb,hv⟩ := transfer_chain
  rw [PV_Src_Forest_BlockCollect.parts_blocks _ _ pt hp 0 (by decide),blockR,hb,okOr_ok]
  exact hv
#print axioms transfer
end R1Z.PV_RunJoin_SourceBlock0020
