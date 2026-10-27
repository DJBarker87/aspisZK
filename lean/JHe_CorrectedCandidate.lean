import JHc_TX1Candidate
import JHc_CorrectedOwnership
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_CorrectedCandidate
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

/-- Returning verifier child on the raw inputs actually selected from the
corrected common TX1 entry. SDK decoding/dispatch/copy/cleanup and checkpoint
identity are separate obligations. -/
theorem source :
    ∃ (stored pub : Slice U8) (saved : alloc.vec.Vec U8),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        (JHb_World.e1.buffers (JHb_World.e1.handles 0).1)
        {start:=688#usize,«end»:=58295#usize}=ok stored ∧
      JHb_World.e1.buffers (JHb_World.e1.handles 1).1=pub ∧
      verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
        pub stored 10#usize () none=ok (.Ok saved) ∧ saved.val.length=1768 := by
  obtain ⟨_p,_scratch,_initial,_out,_pending,_after,_g,_flushed,saved,
    _prepare,_batch,_query,_flush,_write,run,length,_variant,_next,_size⟩ := JHc_TX1Candidate.returns
  exact ⟨JFx_NativeBytes.proof,JFx_NativeBytes.publicInput,saved,
    JHc_CorrectedOwnership.inputs.1,JHc_CorrectedOwnership.inputs.2,run,length⟩
#print axioms source
end AspisR1.JHe_CorrectedCandidate
end
