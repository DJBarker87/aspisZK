import NJC_ReaderResults
set_option autoImplicit false
noncomputable section
namespace NJC_EReaderResults
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open OraclePortCkptAbi2Extracted OraclePortCkptAbi4Decode
open CheckpointBytes3EDecode CheckpointBytes3EShape CheckpointBytes3Word
attribute [local instance] Classical.propDecidable

def naturalE (b : Array U8 32#usize) :
 core.result.Result AspisR1Stage2.aspis_core.field.wide_exact.WideExact verifier.Error :=
 let q := eWords (word32 b.to_slice b.property)
 if CanonicalWide q then .Ok (CheckpointBytes3Namespaces.fromE q) else .Err .Checkpoint

/-- Eight natural little-endian words with the exact canonical guard, full
Ok payload and Checkpoint rejection, matching NJC_readers::read_e. -/
theorem decodeE (b : Array U8 32#usize) :
 (do let q ← decode_e_spec b.to_slice
     ok (CheckpointBytes3Reader.optionE q))=ok (naturalE b) := by
 have source : decode_e_spec b.to_slice =
   if CanonicalWide (eWords (word32 b.to_slice b.property)) then
    ok (some (eWords (word32 b.to_slice b.property))) else ok none := by
  apply e_shape b.to_slice b.property (word32 b.to_slice b.property)
  · simpa [word32] using word_total b.to_slice 0#usize (by change 0+4≤b.val.length;rw [b.property];omega)
  · simpa [word32] using word_total b.to_slice 4#usize (by change 4+4≤b.val.length;rw [b.property];omega)
  · simpa [word32] using word_total b.to_slice 8#usize (by change 8+4≤b.val.length;rw [b.property];omega)
  · simpa [word32] using word_total b.to_slice 12#usize (by change 12+4≤b.val.length;rw [b.property];omega)
  · simpa [word32] using word_total b.to_slice 16#usize (by change 16+4≤b.val.length;rw [b.property];omega)
  · simpa [word32] using word_total b.to_slice 20#usize (by change 20+4≤b.val.length;rw [b.property];omega)
  · simpa [word32] using word_total b.to_slice 24#usize (by change 24+4≤b.val.length;rw [b.property];omega)
  · simpa [word32] using word_total b.to_slice 28#usize (by change 28+4≤b.val.length;rw [b.property];omega)
 rw [source]
 dsimp only [naturalE]
 split_ifs <;> rfl

/-- All pre-states: raw panic/divergence remains explicit until a caller
establishes its bound. No successful child hypothesis. -/
theorem e (r : verifier.Reader) :
 CheckpointBytes3Reader.readE r=
 (do let (b,out) ← CheckpointBytes3Reader.raw 32#usize r
     ok (naturalE b,out)) := by
 unfold CheckpointBytes3Reader.readE
 apply NIL_ResultCases.bind_congr
 rintro ⟨b,out⟩
 have h := decodeE b
 change (do let q ← decode_e_spec b.to_slice
            ok (CheckpointBytes3Reader.optionE q,out))=_
 rw [decode_e_identification b.to_slice b.property]
 rw [decode_e_identification b.to_slice b.property] at h
 change ok (_,out)=_
 exact congrArg (fun q=>ok (q,out)) (Result.ok.inj h)

#print axioms decodeE
#print axioms e
end NJC_EReaderResults
