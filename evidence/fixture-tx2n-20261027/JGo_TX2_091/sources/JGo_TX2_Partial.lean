import JGo_TX2_BatchQuery
import JGo_TX2_FinishPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Partial
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

def writeback (a : verifier.Accumulator) (flushed : Slice K) : verifier.Accumulator :=
  {a with weights := (alloc.vec.Vec.deref_mut a.weights).2 flushed}

def LocalFacts {C Hash : Type} (base : VTop_Stages.Ops) (seed : FinishOps FIo_Install.W)
    (err : C) (geometry : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) : Prop :=
  JGe_View.folded=JGc_TX2_Obstruction70.folded ∧
  ∃ a b flushed,
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
    flushed.val.length=64 ∧ (∀ q∈flushed.val,Port3_FlushInstall.Canonical q) ∧
    ∀ inactive,
      Port4D_FinishInstall.finish (FIo_Install.finishOps (.Ok ()) seed)
        (JGo_TX2_FinishPrefix.view inactive) JFo_Prepared.value (writeback a flushed) none=
      Port3_QueryInstall.result (JGo_TX2_FinishPrefixTools.remaining
        (Port4D_Round.native (FIo_Install.finishOps (.Ok ()) seed))
        (JGo_TX2_FinishPrefix.view inactive) JFo_Prepared.value (writeback a flushed)
        JGo_TX2_WeightData.value JGo_TX2_FinishPrefix.alphas JGo_TX2_Horner1_6.after)

/-- Local non-vacuity: constructed returns share the SAME query-returned a,b
and actual flushed-weight writeback. Pair/dot remain computations, not success
hypotheses. This is not accepted2 or complete deployed non-vacuity. -/
theorem source {C Hash : Type} (base : VTop_Stages.Ops) (seed : FinishOps FIo_Install.W)
    (err : C) (geometry : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    LocalFacts base seed err geometry query D hash := by
  obtain ⟨a,b,flushed,root,batch,updates,call,weights,next,flush,size,canon⟩ :=
    JGo_TX2_BatchQuery.source base err geometry query D hash
  exact ⟨root,a,b,flushed,batch,updates,call,weights,next,flush,size,canon,
    fun inactive=>JGo_TX2_FinishPrefix.installed seed inactive (writeback a flushed)⟩
#print axioms source

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {C Hash : Type} (base : VTop_Stages.Ops) (seed : FinishOps FIo_Install.W)
    (err : C) (geometry : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    LocalFacts base seed err geometry query D hash :=
  ⟨JFn_Resume.on_saved saved same JFp_SHADigest.digest D hash realizes,
    source base seed err geometry query D hash⟩
#print axioms on_saved
end AspisR1.JGo_TX2_Partial
end
