import NMS_R2N_Interpreted
import NMS_ScanLength
set_option autoImplicit false
noncomputable section
namespace NMS_R2N_ScanSites
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal
variable {M : Type → Type} [Monad M] [MonadLift Result M]
local instance : MonadLift Result Result where
 monadLift := id
/-- Frozen scan_proof_buffer: Box::new is AFTER decoding and BEFORE encoding,
comparison and tag. The successful candidate payload survives unchanged. -/
def scan (allocate : M Unit) (bytes : Slice U8) : M (core.result.Result
 AdapterRw.r1_pool_adapter.ScannedAsqaProof AdapterRw.solana_program_error.ProgramError) := do
 let expected ← lift (Usize.checked_add 688#usize 57607#usize)
 match expected with
 | none => ok (.Err .InvalidAccountData)
 | some size =>
   if Slice.len bytes != size then ok (.Err .InvalidAccountData) else do
    let header ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
     bytes {start:=0#usize,«end»:=688#usize}
    let decoded ← decode_pool_v1_pair_verified_afterstate_v1 header
    match decoded with
    | .Err _ => ok (.Err .InvalidAccountData)
    | .Ok candidate =>
      let _ ← allocate
      let encoded ← encode_pool_v1_pair_verified_afterstate_v1 candidate
      match encoded with
      | .Err _ => ok (.Err .InvalidAccountData)
      | .Ok encoded =>
        if encoded.val != header.val then ok (.Err .InvalidAccountData) else do
         let tag ← Slice.index_usize bytes 696#usize
         if tag != 2#u8 then ok (.Err .InvalidAccountData) else
          ok (.Ok ⟨AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1 candidate,57607#usize⟩)

def interpreted (bytes : Slice U8) := scan (M := RSL.Spec) RSL.Spec.alloc bytes

/-- Exact value projection to the CLOSED scanner source. The allocation
operation is interpreted separately by the retained std/allocator item. -/
theorem erases (bytes : Slice U8) :
 scan (M := Result) (ok ()) bytes = AspisR1.NFY_JHf_Scan.source bytes := by
 unfold scan AspisR1.NFY_JHf_Scan.source
 simp only [bind_tc_ok]
 rfl
#print axioms erases
end NMS_R2N_ScanSites
