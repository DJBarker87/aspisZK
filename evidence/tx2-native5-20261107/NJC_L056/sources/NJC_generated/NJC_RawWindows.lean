import NJC_RawPort
set_option autoImplicit false
noncomputable section
namespace NJC_RawWindows
open Aeneas Aeneas.Std Result NIL_Carriers

/-- Generic same-window lifting of the freshly emitted K reader. The opaque
parser is called on identical bytes; every Option/error/fail/div arm is kept.
Concrete debug unwrap identification remains an explicit separate obligation. -/
theorem k
 (unwrap : core.result.Result (Array U8 16#usize) core.array.TryFromSliceError → Result (Array U8 16#usize))
 (unwrap_ok : ∀ b,unwrap (.Ok b)=ok b)
 (parse : Slice U8 → Result (Option Fresh.K))
 (r : Fresh.R) (bound : r.at.val+16≤r.bytes.val.length) :
 ∃ b : Array U8 16#usize, ∃ out : Fresh.R,
 b.val=(r.bytes.val.drop r.at.val).take 16 ∧
 out.at.val=r.at.val+16 ∧ out.bytes=r.bytes ∧
 NJC_ReaderEmission.verifier.Reader.k unwrap parse r=
 (do let (reply,_) ← NJC_ReaderEmission.verifier.Reader.k unwrap parse
       {bytes:=b.to_slice,«at»:=0#usize}
     ok (reply,out)) := by
 obtain ⟨b,out,run,contents,cursor,backing⟩ := NJC_RawPort.bounded 16#usize unwrap unwrap_ok r bound
 obtain ⟨b',out',run',contents',_,_⟩ := NJC_RawPort.bounded 16#usize unwrap unwrap_ok
  {bytes:=b.to_slice,«at»:=0#usize} (by simpa using b.property.ge)
 have same : b'=b := by
  apply Subtype.ext
  change b'.val=(b.val.drop 0).take 16 at contents'
  have length : b.val.length=16 := b.property
  simpa only [List.drop_zero,List.take_of_length_le length.le] using contents'
 subst b'
 refine ⟨b,out,contents,cursor,backing,?_⟩
 unfold NJC_ReaderEmission.verifier.Reader.k
 rw [run,run']
 simp only [bind_tc_ok,lift]
 dsimp only
 cases h:parse b.to_slice with
 | fail err => rfl
 | div => rfl
 | ok value => cases value <;> rfl

theorem e
 (unwrap : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError → Result (Array U8 32#usize))
 (unwrap_ok : ∀ b,unwrap (.Ok b)=ok b)
 (parse : Slice U8 → Result (Option Fresh.E))
 (r : Fresh.R) (bound : r.at.val+32≤r.bytes.val.length) :
 ∃ b : Array U8 32#usize, ∃ out : Fresh.R,
 b.val=(r.bytes.val.drop r.at.val).take 32 ∧
 out.at.val=r.at.val+32 ∧ out.bytes=r.bytes ∧
 NJC_ReaderEmission.verifier.Reader.e unwrap parse r=
 (do let (reply,_) ← NJC_ReaderEmission.verifier.Reader.e unwrap parse
       {bytes:=b.to_slice,«at»:=0#usize}
     ok (reply,out)) := by
 obtain ⟨b,out,run,contents,cursor,backing⟩ := NJC_RawPort.bounded 32#usize unwrap unwrap_ok r bound
 obtain ⟨b',out',run',contents',_,_⟩ := NJC_RawPort.bounded 32#usize unwrap unwrap_ok
  {bytes:=b.to_slice,«at»:=0#usize} (by simpa using b.property.ge)
 have same : b'=b := by
  apply Subtype.ext
  change b'.val=(b.val.drop 0).take 32 at contents'
  have length : b.val.length=32 := b.property
  simpa only [List.drop_zero,List.take_of_length_le length.le] using contents'
 subst b'
 refine ⟨b,out,contents,cursor,backing,?_⟩
 unfold NJC_ReaderEmission.verifier.Reader.e
 rw [run,run']
 simp only [bind_tc_ok,lift]
 dsimp only
 cases h:parse b.to_slice with
 | fail err => rfl
 | div => rfl
 | ok value => cases value <;> rfl

#print axioms k
#print axioms e
end NJC_RawWindows
