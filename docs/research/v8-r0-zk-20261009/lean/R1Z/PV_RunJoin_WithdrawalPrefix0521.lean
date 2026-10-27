import R1Z.PV_RunJoin_WithdrawalPrefix0421
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WithdrawalPrefix0521
open R0Z.WriterRefine PV_RunJoin_FixtureRecords PV_RunJoin_AppendNative17
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation
/-- One symbolic append step; the already certified source node is never unfolded. -/
theorem source : digK (K := M) withdrawal5 =
    AspisR1.AppendPath.pathPrefix (base true) (outputPair true) 5 := by
  have h := PV_RunJoin_NodeResult21.field _ _ _
    (PV_Src_CanonicalRoots.canonical (Fin.castSucc (⟨4,by decide⟩ : Fin 20)))
    PV_RunJoin_AppendNative17.withdrawal_node4
  change R0P.nodeCompress (digK (K := M) withdrawal4)
    (digK (K := M) (PV_Src_CanonicalRoots.table.val[4]!)) = digK withdrawal5 at h
  rw [PV_RunJoin_AppendShape21.empty ⟨4,by decide⟩] at h
  rw [PV_RunJoin_AppendShape21.step_zero (base true) rfl (outputPair true) ⟨4,by decide⟩,
    ← PV_RunJoin_WithdrawalPrefix0421.source]
  exact h.symm
#print axioms source
end R1Z.PV_RunJoin_WithdrawalPrefix0521
