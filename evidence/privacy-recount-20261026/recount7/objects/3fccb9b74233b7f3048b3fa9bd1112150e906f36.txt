import R1Z.PV_RunJoin_NodeShape20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeExecution20
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_RunJoin_BankCertificate19
open PV_Src_Forest_PrimitiveArguments
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder

theorem chain (w : RW) (p : RP) (b : Nat) (c : Certificate)
    (hn : NodeKind b)
    (hp : R0BlockCopies.node_pre ((rustChunks (wordWitness w) (wordPublic p)).right b) = ok c.pre)
    (ha : R0BlockCopies.node_absorb ((rustChunks (wordWitness w) (wordPublic p)).left b) = ok c.absorption)
    (hw : ∃ block, (do
      let rounds ← R0PoseidonCopy.perm_rounds c.pre c.absorption
      R0BlockCopies.write_block c.pre c.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]!) :
    ∃ block, RustWriterChain (wordPublic p).variant (rustChunks (wordWitness w) (wordPublic p)) b = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  obtain ⟨block,hb,hv⟩ := hw
  refine ⟨block,?_,hv⟩
  rw [RustWriterChain,if_pos hn,hp]
  simp only [bind_tc_ok]
  rw [ha]
  simp only [bind_tc_ok]
  exact hb
#print axioms chain
end R1Z.PV_RunJoin_NodeExecution20
