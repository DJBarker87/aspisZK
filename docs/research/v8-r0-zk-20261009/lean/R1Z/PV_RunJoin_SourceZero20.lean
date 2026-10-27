import R1Z.PV_RunJoin_ZeroCopy20
import R1Z.PV_RunJoin_PartsBlock20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceZero20
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev c := PV_RunJoin_BankZero19.certificate

theorem chain (b : Nat) (hlo : 27 ≤ b) (hhi : b ≤ 29) : ∃ block,
    RustWriterChain (wordPublic withdrawalPublic).variant
      (rustChunks (wordWitness withdrawalWitness) (wordPublic withdrawalPublic)) b = ok block ∧
    ∀ row, row < 16 → ∀ lane, lane < 16 → block.val[row*16+lane]! = (c.row row).val[lane]! := by
  have hn : ¬ NodeKind b := by unfold NodeKind;omega
  have hz : ZeroKind (wordPublic withdrawalPublic).variant b := by
    change ZeroKind R0P.Variant.withdrawal b
    exact ⟨rfl,hlo,hhi⟩
  rw [RustWriterChain,if_neg hn,if_pos hz]
  exact PV_RunJoin_ZeroCopy20.writer
#print axioms chain

theorem rows (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt)
    (b : Nat) (hlo : 27 ≤ b) (hhi : b ≤ 29) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[b]!).val[row*16+lane]! = (c.row row).val[lane]! :=
  PV_RunJoin_PartsBlock20.source _ _ b (by omega) c (chain b hlo hhi) pt hp
#print axioms rows

theorem block27 (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[27]!).val[row*16+lane]! = (c.row row).val[lane]! := rows pt hp 27 (by decide) (by decide)
theorem block28 (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[28]!).val[row*16+lane]! = (c.row row).val[lane]! := rows pt hp 28 (by decide) (by decide)
theorem block29 (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ row, row < 16 → ∀ lane, lane < 16 → (pt.blocks.val[29]!).val[row*16+lane]! = (c.row row).val[lane]! := rows pt hp 29 (by decide) (by decide)
#print axioms block27
#print axioms block28
#print axioms block29
end R1Z.PV_RunJoin_SourceZero20
