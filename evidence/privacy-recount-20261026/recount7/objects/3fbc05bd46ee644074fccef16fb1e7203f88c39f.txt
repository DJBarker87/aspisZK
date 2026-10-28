import R1Z.PV_RunJoin_WithdrawalPrefix1821
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WithdrawalPrefix1921
open R0Z.WriterRefine PV_RunJoin_FixtureRecords PV_RunJoin_AppendNative17
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation
/-- One symbolic append step; the already certified source node is never unfolded. -/
theorem source : digK (K := M) withdrawal19 =
    AspisR1.AppendPath.pathPrefix (base true) (outputPair true) 19 := by
  have h := PV_RunJoin_NodeResult21.field _ _ _
    (PV_Src_CanonicalRoots.canonical (Fin.castSucc (⟨18,by decide⟩ : Fin 20)))
    PV_RunJoin_AppendNative17.withdrawal_node18
  change R0P.nodeCompress (digK (K := M) withdrawal18)
    (digK (K := M) (PV_Src_CanonicalRoots.table.val[18]!)) = digK withdrawal19 at h
  rw [PV_RunJoin_AppendShape21.empty ⟨18,by decide⟩] at h
  rw [PV_RunJoin_AppendShape21.step_zero (base true) rfl (outputPair true) ⟨18,by decide⟩,
    ← PV_RunJoin_WithdrawalPrefix1821.source]
  exact h.symm
#print axioms source
end R1Z.PV_RunJoin_WithdrawalPrefix1921
