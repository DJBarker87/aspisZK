import R1Z.PV_RunJoin_FixturePathInputs16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TreeValue16
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M

theorem unique (d target : Array U32 8#usize) (hc : Canon8 d) (ht : Canon8 target)
    (hl : DigestLift d (digK (K := M) target)) : d = target := by
  apply BuilderRecordCanonical.array_ext
  intro j hj
  have bound : j < 8 := by simpa using hj
  exact PV_RunJoin_LeafLift16.word_injective (hc j bound) (ht j bound) (hl ⟨j,bound⟩)

theorem transfer (n : Usize) (hn : n.val ≤ 24) (target : Array U32 8#usize)
    (ht : Canon8 target)
    (hm : R0P.merkleRootAux (R0P.digestOf PV_RunJoin_FixtureHashModel.s_3_23)
      PV_RunJoin_FixtureRecords.path n.val = digK (K := M) target) :
    tree_cur_r transferWitness transferPublic n = ok target := by
  obtain ⟨d,hd,hl,hc⟩ := PV_RunJoin_TreeLift16.tree
    (PV_Src_Forest_PrimitiveArguments.wordWitness transferWitness)
    (PV_Src_Forest_PrimitiveArguments.wordPublic transferPublic)
    (PV_RunJoin_FixtureRecords.base false) (by rfl) transfer_checked n.val hn
  rw [PV_RunJoin_FixturePathInputs16.transfer_tree,hm] at hl
  rw [PV_Src_Forest_TreeArguments.tree _ _ n hn]
  exact hd.trans (congrArg Result.ok (unique d target hc ht hl))
#print axioms transfer

theorem withdrawal (n : Usize) (hn : n.val ≤ 24) (target : Array U32 8#usize)
    (ht : Canon8 target)
    (hm : R0P.merkleRootAux (R0P.digestOf PV_RunJoin_FixtureHashModel.s_3_23)
      PV_RunJoin_FixtureRecords.path n.val = digK (K := M) target) :
    tree_cur_r withdrawalWitness withdrawalPublic n = ok target := by
  obtain ⟨d,hd,hl,hc⟩ := PV_RunJoin_TreeLift16.tree
    (PV_Src_Forest_PrimitiveArguments.wordWitness withdrawalWitness)
    (PV_Src_Forest_PrimitiveArguments.wordPublic withdrawalPublic)
    (PV_RunJoin_FixtureRecords.base false) (by rfl) withdrawal_checked n.val hn
  rw [PV_RunJoin_FixturePathInputs16.withdrawal_tree,hm] at hl
  rw [PV_Src_Forest_TreeArguments.tree _ _ n hn]
  exact hd.trans (congrArg Result.ok (unique d target hc ht hl))
#print axioms withdrawal
#print axioms unique
end R1Z.PV_RunJoin_TreeValue16
