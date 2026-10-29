import R1Z.PV_RDB2E_DispatchCallbacks
import R1Z.PV_RDB2E_FallbackBlockTotal
namespace R1Z.PV_RDB2F_ConcreteSoft
open Aeneas Aeneas.Std Result PV_RDB2E_ShaHandles
set_option autoImplicit false

/-- Concrete owned software word-block projection. Invalid list lengths have
an explicit failure branch; native padding always supplies full64-byte blocks.
Outer soft::compress iterator/copy/refinement is still a separate obligation. -/
def software (state : State) (block : List U8) : Result State :=
  if h : block.length=64 then do
    let words ← PV_CBL_ShaBytes.sha_load64 ⟨block,h⟩
    PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state words
  else fail .panic

theorem wrong_length (state : State) (block : List U8) (h : block.length≠64) :
    software state block=fail .panic := by simp only [software,dif_neg h]

theorem fixed_block (state : State) (block : Array U8 64#usize) :
    software state block.val=
      (do let words ← PV_CBL_ShaBytes.sha_load64 block
          PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state words) := by
  unfold software
  split
  · rfl
  · rename_i bad
    exact False.elim (bad (show block.val.length = 64 from block.property))

theorem word_block_total (state : State) (words : Array U32 16#usize) :
    ∃ after, PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state words=ok after :=
  PV_CBL_FallbackBlockTotal.total state words

/-- Complete four-field model equality with an actual software projection,
not an arbitrary compression parameter or a compression-success hypothesis. -/
theorem all_fields (f : Frame) (valid : (position f).val<64) :
    (do let after ← finalize software f valid;ok (forget after))=
      PV_RDB2D_SHAState.completeState software f.core f.buffer (position f) := by
  rw [complete_typed software f valid]
  exact PV_RDB2D_SHAState.all_mutable_fields software f.core f.buffer (position f) f.output valid

/-- The reachable hardware case stays explicit and uninstantiated. -/
theorem both_backends (backend : PV_RDB2E_Dispatch.Backend)
    (shani : State → List U8 → Result State) (f : Frame) (valid : (position f).val<64) :
    (do let after ← finalize (PV_RDB2E_Dispatch.select backend software shani) f valid
        ok (forget after))=
      PV_RDB2D_SHAState.completeState (PV_RDB2E_Dispatch.select backend software shani)
        f.core f.buffer (position f) := by
  rw [complete_typed]
  exact PV_RDB2D_SHAState.all_mutable_fields _ _ _ _ _ valid

#print axioms wrong_length
#print axioms fixed_block
#print axioms word_block_total
#print axioms all_fields
#print axioms both_backends
end R1Z.PV_RDB2F_ConcreteSoft
