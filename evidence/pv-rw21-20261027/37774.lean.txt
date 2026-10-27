import R1Z.ProverRw21FlatSourceLaw
import R1Z.ProverRw21WideCarrier
import R1Z.ProverRw21ByteCarrier
import R1Z.ProverRw18CanonicalBytes
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21WideImage
open Aeneas Aeneas.Std ProverRwFull
open ProverRw21ByteCarrier
open AspisR1.RetainedFieldByteCodec

/-- Split only the two quartic halves, keeping all word values symbolic. -/
theorem split (x : ProverRw21WideCarrier.W) : ProverRw21FlatOutput.bytes x =
    ProverRw18QuarticBytes.bytes x.c0 ++ ProverRw18QuarticBytes.bytes x.c1 := by
  simp only [ProverRw21FlatOutput.bytes,ProverRw18QuarticBytes.bytes,
    ProverRw18ComplexBytes.bytes,ProverRw18ComplexWrite.word,Array.to_slice,List.append_assoc]

theorem quarter_image (x : ProverRw18FieldMeaning.Q) (h : ProverRw18FullCarrier.canonical x) :
    (ProverRw18QuarticBytes.bytes x).map decode =
      List.ofFn (fun i => UInt8.ofFin (encodeQM31LE
        (ProverCommitLimbBytes47.limbs (ProverRw18FullCarrier.raw x) h) i)) := by
  have hs := ProverRw18CanonicalBytes.image (ProverRw18FullCarrier.raw x) h
  rw [ProverRw18FullCarrier.full_raw] at hs
  have hh := congrArg (List.map UInt8.ofFin) hs
  rw [List.map_map,List.map_ofFn] at hh
  exact hh

theorem raw_image (x : ProverRw21WideCarrier.W) (h : ProverRw21WideCarrier.canonical x) :
    (ProverRw21FlatOutput.bytes x).map decode =
      List.ofFn (ProverCommitWideBytes48.sourceCell (ProverRw21WideCarrier.raw x) h) := by
  rw [split,List.map_append,quarter_image x.c0 h.1,quarter_image x.c1 h.2]
  unfold ProverCommitWideBytes48.sourceCell
  rw [List.ofFn_fin_append]
  rfl

theorem mathematical_image (x : ProverRw21WideCarrier.W) (h : ProverRw21WideCarrier.canonical x) :
    (ProverRw21FlatOutput.bytes x).map decode =
      ProverRw21ProtocolOutput.wide (ProverRw21WideCarrier.value x) := by
  rw [raw_image x h,ProverRw21WideCarrier.source_cell]
  rfl

theorem source_image (x : ProverRw21WideCarrier.W) (h : ProverRw21WideCarrier.canonical x) :
    ∃ result, ProverRwP6FlatSource.wide_bytes_flat x=.ok result ∧
      result.val.map decode=ProverRw21ProtocolOutput.wide (ProverRw21WideCarrier.value x) :=
  ⟨ProverRw21FlatOutput.output x,ProverRw21FlatSourceLaw.exact x,mathematical_image x h⟩

#print axioms split
#print axioms quarter_image
#print axioms raw_image
#print axioms mathematical_image
#print axioms source_image
end R1Z.ProverRw21WideImage
