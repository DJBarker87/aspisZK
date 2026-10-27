import R1Z.PV_RunJoin_TransferPrefix0921
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TransferPrefix1021
open R0Z.WriterRefine PV_RunJoin_FixtureRecords PV_RunJoin_AppendNative17
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation
/-- One symbolic append step; the already certified source node is never unfolded. -/
theorem source : digK (K := M) transfer10 =
    AspisR1.AppendPath.pathPrefix (base false) (outputPair false) 10 := by
  have h := PV_RunJoin_NodeResult21.field _ _ _
    (PV_Src_CanonicalRoots.canonical (Fin.castSucc (⟨9,by decide⟩ : Fin 20)))
    PV_RunJoin_AppendNative17.transfer_node9
  change R0P.nodeCompress (digK (K := M) transfer9)
    (digK (K := M) (PV_Src_CanonicalRoots.table.val[9]!)) = digK transfer10 at h
  rw [PV_RunJoin_AppendShape21.empty ⟨9,by decide⟩] at h
  rw [PV_RunJoin_AppendShape21.step_zero (base false) rfl (outputPair false) ⟨9,by decide⟩,
    ← PV_RunJoin_TransferPrefix0921.source]
  exact h.symm
#print axioms source
end R1Z.PV_RunJoin_TransferPrefix1021
