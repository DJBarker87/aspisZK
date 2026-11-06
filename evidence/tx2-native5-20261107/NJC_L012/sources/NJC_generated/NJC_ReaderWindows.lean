import NJC_ReaderResults
set_option autoImplicit false
noncomputable section
namespace NJC_ReaderWindows
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Window32 transport for the complete E reply, including canonical rejection.
The actual post Reader is proved from its emitted raw call, not seeded by an
oracle or inferred from a matching address. -/
theorem e (r : verifier.Reader) (bound : r.at.val+32≤r.bytes.val.length) :
 ∃ b : Array U8 32#usize, ∃ out : verifier.Reader,
 b.val=(r.bytes.val.drop r.at.val).take 32 ∧
 out.at.val=r.at.val+32 ∧ out.bytes=r.bytes ∧
 CheckpointBytes3Reader.readE r=
 (do let (reply,_) ← CheckpointBytes3Reader.readE {bytes:=b.to_slice,«at»:=0#usize}
     ok (reply,out)) := by
 obtain ⟨b,out,contents,cursor,backing,run⟩ := CheckpointBytes3Reader.read_e_c5 r bound
 obtain ⟨b',out',contents',_,_,run'⟩ := CheckpointBytes3Reader.read_e_c5
  {bytes:=b.to_slice,«at»:=0#usize} (by simpa using b.property.ge)
 have same : b'=b := by
  apply Subtype.ext
  simpa only [List.drop_zero,List.take_of_length_le b.property.le] using contents'
 subst b'
 refine ⟨b,out,contents,cursor,backing,?_⟩
 rw [run,run']
 rfl

/-- Full K window plus full emitted backing frame, lifting the bounded16-byte
native check to every entered checkpoint read. No successful-reply premise. -/
theorem k (r : verifier.Reader) (bound : r.at.val+16≤r.bytes.val.length) :
 ∃ b : Array U8 16#usize, ∃ out : verifier.Reader,
 b.val=(r.bytes.val.drop r.at.val).take 16 ∧
 out.at.val=r.at.val+16 ∧ out.bytes=r.bytes ∧
 CheckpointBytes3Reader.readK r=
 (do let (reply,_) ← CheckpointBytes3Reader.readK {bytes:=b.to_slice,«at»:=0#usize}
     ok (reply,out)) := by
 obtain ⟨b,out,contents,cursor,backing,run⟩ := NJC_ReaderResults.boundedK r bound
 obtain ⟨b',out',contents',_,_,run'⟩ := NJC_ReaderResults.boundedK
  {bytes:=b.to_slice,«at»:=0#usize} (by simpa using b.property.ge)
 have same : b'=b := by
  apply Subtype.ext
  simpa only [List.drop_zero,List.take_of_length_le b.property.le] using contents'
 subst b'
 refine ⟨b,out,contents,cursor,backing,?_⟩
 rw [run,run']
 rfl

/-- Raw reads preserve every backing byte on every bounded input. This is the
frame needed to install the selected window at the SAME caller location. -/
theorem raw (n : Usize) (r : verifier.Reader) (bound : r.at.val+n.val≤r.bytes.val.length) :
 ∃ b : Array U8 n, ∃ out : verifier.Reader,
 b.val=(r.bytes.val.drop r.at.val).take n.val ∧
 out.at.val=r.at.val+n.val ∧ out.bytes=r.bytes ∧
 CheckpointBytes3Reader.raw n r=ok (b,out) := by
 obtain ⟨b,out,run,contents,cursor,backing⟩ :=
  OraclePortCkptAbi2Unwrap.raw_panic_unreachable r n (fun _=>fail .panic) bound
 exact ⟨b,out,contents,cursor,backing,run⟩

#print axioms e
#print axioms k
#print axioms raw
end NJC_ReaderWindows
