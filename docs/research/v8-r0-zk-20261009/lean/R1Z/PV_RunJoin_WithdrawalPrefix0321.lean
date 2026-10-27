import R1Z.PV_RunJoin_WithdrawalPrefix0221
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WithdrawalPrefix0321
open R0Z.WriterRefine PV_RunJoin_FixtureRecords PV_RunJoin_AppendNative17
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation
/-- One symbolic append step; the already certified source node is never unfolded. -/
theorem source : digK (K := M) withdrawal3 =
    AspisR1.AppendPath.pathPrefix (base true) (outputPair true) 3 := by
  have h := PV_RunJoin_NodeResult21.field _ _ _
    (PV_Src_CanonicalRoots.canonical (Fin.castSucc (⟨2,by decide⟩ : Fin 20)))
    PV_RunJoin_AppendNative17.withdrawal_node2
  change R0P.nodeCompress (digK (K := M) withdrawal2)
    (digK (K := M) (PV_Src_CanonicalRoots.table.val[2]!)) = digK withdrawal3 at h
  rw [PV_RunJoin_AppendShape21.empty ⟨2,by decide⟩] at h
  rw [PV_RunJoin_AppendShape21.step_zero (base true) rfl (outputPair true) ⟨2,by decide⟩,
    ← PV_RunJoin_WithdrawalPrefix0221.source]
  exact h.symm
#print axioms source
end R1Z.PV_RunJoin_WithdrawalPrefix0321
