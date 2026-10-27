import R1Z.PV_RunJoin_TransferPrefix1921
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TransferPrefix2021
open R0Z.WriterRefine PV_RunJoin_FixtureRecords PV_RunJoin_AppendNative17
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation
/-- One symbolic append step; the already certified source node is never unfolded. -/
theorem source : digK (K := M) transfer20 =
    AspisR1.AppendPath.pathPrefix (base false) (outputPair false) 20 := by
  have h := PV_RunJoin_NodeResult21.field _ _ _
    (PV_Src_CanonicalRoots.canonical (Fin.castSucc (⟨19,by decide⟩ : Fin 20)))
    PV_RunJoin_AppendNative17.transfer_node19
  change R0P.nodeCompress (digK (K := M) transfer19)
    (digK (K := M) (PV_Src_CanonicalRoots.table.val[19]!)) = digK transfer20 at h
  rw [PV_RunJoin_AppendShape21.empty ⟨19,by decide⟩] at h
  rw [PV_RunJoin_AppendShape21.step_zero (base false) rfl (outputPair false) ⟨19,by decide⟩,
    ← PV_RunJoin_TransferPrefix1921.source]
  exact h.symm
#print axioms source
end R1Z.PV_RunJoin_TransferPrefix2021
