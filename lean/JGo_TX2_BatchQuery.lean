import JGo_TX2_Root
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_BatchQuery
open Aeneas Aeneas.Std Result

/-- The actual installed batch and query/flush returns share one Prepared and
one retained proof. The existential accumulator is the query's own return. -/
theorem source (base : VTop_Stages.Ops) {C Hash : Type} (err : C)
    (geometry : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    ∃ a b flushed,
      JGe_View.folded=JGc_TX2_Obstruction70.folded ∧
      Op5T_Install.stageBatch Port4B_Install.leaves
        (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
        JFx_NativeBytes.proof JFo_Prepared.value JGe_View.folded 1#usize hash=ok (.Ok ()) ∧
      JFz_TX2_AccumulationChain.updates (JGc_TX2_QueryDictionary.input query) 12=ok (a,b) ∧
      (Tx2N_Install.inner base true (JGc_TX2_InstalledQuery.raw query)).op6
        JFx_NativeBytes.proof JFo_Prepared.value JFo_Prepared.accumulator
        JFr_TX2_Powers.value none (JFv_TX2_Geometry.value err geometry)
        JFo_Pending.value 22#usize=ok (.Ok (a,b)) ∧
      a.weights=JFo_Prepared.accumulator.weights ∧ a.next=22#usize ∧
      (Tx2N_Install.inner base true (JGc_TX2_InstalledQuery.raw query)).op9
        b a.weights.deref=ok flushed ∧
      flushed.val.length=64 ∧ ∀ q∈flushed.val,Port3_FlushInstall.Canonical q := by
  obtain ⟨a,b,flushed,updates,call,weights,next,flush,size,canon⟩ :=
    JGc_TX2_InstalledQuery.source base err geometry query
  exact ⟨a,b,flushed,JGo_TX2_Root.selected,
    JGo_TX2_Root.selected.symm ▸ JGm_TX2_Batch.source D hash,
    updates,call,weights,next,flush,size,canon⟩
#print axioms source
end AspisR1.JGo_TX2_BatchQuery
end
