import R1Z.PV_RunJoin_CertificateExecution20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PartsBlock20
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_RunJoin_CopyCertificate20 PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
open PV_Src_Forest_PrimitiveArguments
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder

theorem source (w : RW) (p : RP) (b : Nat) (hb : b < 57) (c : Certificate)
    (chain : ∃ block, RustWriterChain (wordPublic p).variant (rustChunks (wordWitness w) (wordPublic p)) b = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]!)
    (pt : Parts) (hp : parts w p = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[b]!).val[row*16+lane]! = (c.row row).val[lane]! := by
  obtain ⟨block,hc,hv⟩ := chain
  rw [PV_Src_Forest_BlockCollect.parts_blocks _ _ pt hp b hb,blockR,hc,okOr_ok]
  exact hv
#print axioms source

theorem sponge (w : RW) (p : RP) (b : Nat) (c : Certificate)
    (hn : ¬ NodeKind b) (hz : ¬ ZeroKind (wordPublic p).variant b)
    (hp : spongePre (rustChunks (wordWitness w) (wordPublic p)) b = ok c.pre)
    (ha : R0BlockCopies.sponge_absorb ((rustChunks (wordWitness w) (wordPublic p)).schunk b)
      ((rustChunks (wordWitness w) (wordPublic p)).sclen b) = ok c.absorption)
    (hw : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds c.pre c.absorption
      R0BlockCopies.write_block c.pre c.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]!) :
    ∃ block, RustWriterChain (wordPublic p).variant (rustChunks (wordWitness w) (wordPublic p)) b = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  obtain ⟨block,hb,hv⟩ := hw
  refine ⟨block,?_,hv⟩
  rw [RustWriterChain,if_neg hn,if_neg hz,hp]
  simp only [bind_tc_ok]
  rw [ha]
  simp only [bind_tc_ok]
  exact hb
#print axioms sponge
end R1Z.PV_RunJoin_PartsBlock20
