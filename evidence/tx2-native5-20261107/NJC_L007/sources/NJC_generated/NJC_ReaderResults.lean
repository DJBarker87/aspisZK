import NID_BoundedReaders
import NIL_ResultCases
set_option autoImplicit false
noncomputable section
namespace NJC_ReaderResults
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open OraclePortCkptAbi2Extracted OraclePortCkptAbi4Decode CheckpointBytes3KDecode CheckpointBytes3ScalarShape
attribute [local instance] Classical.propDecidable

/-- Full four-word reply asserted by NJC_readers::k, not a selected limb.
Canonicality rejection is the actual Checkpoint error. The native assertion
includes all four words on Ok, the exact Err, and cursor/backing descriptor.
Harness SHA is in NJC_SOURCE_PINS.json, key NJC_readers.rs. -/
def naturalK (b : Array U8 16#usize) :
 core.result.Result AspisR1Stage2.aspis_core.field.QM31 verifier.Error :=
 let q := kWords (word b.to_slice b.property 0) (word b.to_slice b.property 1)
   (word b.to_slice b.property 2) (word b.to_slice b.property 3)
 if Canonical q then .Ok (CheckpointBytes3Namespaces.fromK q) else .Err .Checkpoint

theorem decodeK (b : Array U8 16#usize) :
 (do let q ← decode_k_spec b.to_slice
     ok (CheckpointBytes3Reader.optionK q))=ok (naturalK b) := by
 have h := CheckpointBytes3KDecode.decode_k_identification b.to_slice b.property
 rw [CheckpointBytes3KDecode.fixed_decode,CheckpointBytes3KDecode.model_shape
   (CheckpointBytes3KDecode.fixed b.to_slice b.property)
   (word b.to_slice b.property) (CheckpointBytes3KDecode.word_model b.to_slice b.property)] at h
 rw [h]
 unfold naturalK
 split <;> rfl

/-- Full Reader result at every pre-state, including raw panic/divergence.
The supplied bound is needed only to rule out those arms at actual callers. -/
theorem k (r : verifier.Reader) :
 CheckpointBytes3Reader.readK r=
 (do let (b,out) ← CheckpointBytes3Reader.raw 16#usize r
     ok (naturalK b,out)) := by
 unfold CheckpointBytes3Reader.readK
 apply NIL_ResultCases.bind_congr
 rintro ⟨b,out⟩
 have h := decodeK b
 change (do let q ← decode_k_spec b.to_slice
            ok (CheckpointBytes3Reader.optionK q,out))=_
 rw [CheckpointBytes3KDecode.decode_k_identification b.to_slice b.property]
 rw [CheckpointBytes3KDecode.decode_k_identification b.to_slice b.property] at h
 change ok (_,out)=_
 exact congrArg (fun x=> x.map (fun q=>(q,out))) h

/-- No native descriptor-to-content inference: this exact frame is derived
from the emitted raw reader and retained codec law on the SAME bytes. -/
theorem boundedK (r : verifier.Reader) (bound : r.at.val+16≤r.bytes.val.length) :
 ∃ b : Array U8 16#usize, ∃ out : verifier.Reader,
 b.val=(r.bytes.val.drop r.at.val).take 16 ∧
 out.at.val=r.at.val+16 ∧ out.bytes=r.bytes ∧
 CheckpointBytes3Reader.readK r=ok (naturalK b,out) := by
 obtain ⟨b,out,run,contents,cursor,backing⟩ :=
  OraclePortCkptAbi2Unwrap.raw_panic_unreachable r 16#usize (fun _=>fail .panic) bound
 refine ⟨b,out,contents,cursor,backing,?_⟩
 rw [k]
 change (do let (b,out) ← verifier.Reader.rawWithUnwrap 16#usize _ r
            ok (naturalK b,out))=_
 rw [run]
 rfl

#print axioms decodeK
#print axioms k
#print axioms boundedK
end NJC_ReaderResults
