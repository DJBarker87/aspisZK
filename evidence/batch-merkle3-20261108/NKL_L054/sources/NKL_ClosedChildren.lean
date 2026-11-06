import NHV_NET_ParserComposed
import NEO_TailRef.Funs
import S8OwnedP6StrictParser
import NKL_CanonicalKCarrier
import NKB_CanonicalScalarBridge
import NKB_CanonicalRows
set_option autoImplicit false
noncomputable section
namespace NKL_ClosedChildren
open Aeneas Aeneas.Std Result AspisR1
open RetainedFieldByteCodec CheckpointBytes3KDecode

def qToCaller (x : S8OwnedP6.aspis_core.field.QM31) : NKB_CanonicalRange.K :=
 ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩

theorem scalar (b : Array U8 4#usize) :
 S8OwnedP6.aspis_core.field.M31.from_le_bytes b=ok (NKB_CanonicalScalarBridge.scalar b) := by
 have same : S8OwnedP6.aspis_core.field.M31.from_le_bytes b=
  AspisR1M31Parser.field.M31.from_le_bytes b := by
  unfold S8OwnedP6.aspis_core.field.M31.from_le_bytes AspisR1M31Parser.field.M31.from_le_bytes
   S8OwnedP6.aspis_core.field.P AspisR1M31Parser.field.P
  rfl
 rw [same,NKB_CanonicalScalarBridge.source]

/-- Full nominal K payload and both Option arms, from the actual CLOSED
NET/S8 decoder, transferred to this emitted caller's carrier at SAME16 bytes. -/
theorem actualK (b : Array U8 16#usize) :
 NKL_CanonicalKCarrier.mapResult (Option.map qToCaller)
  (S8OwnedP6.aspis_core.field.QM31.from_le_bytes b.to_slice)=
 ok (NKL_CanonicalKCarrier.selected b.to_slice) := by
 have repr : CandidateParserByteOrder.arrayBytes16 b=fixed b.to_slice b.property := by
  funext i
  rfl
 have actual:=S8OwnedP6StrictParser.source_refines b
 rw [repr] at actual
 have raw : OraclePortCkptAbi2Extracted.decode_k_spec b.to_slice=
  ok ((decodeQM31LE (fixed b.to_slice b.property)).map rawLimbs) := by
  rw [decode_k_identification b.to_slice b.property,fixed_decode b.to_slice b.property]
 have selected:=NKL_CanonicalKCarrier.decoder b.to_slice b.property
 rw [raw] at selected
 rw [actual]
 simpa only [NKL_CanonicalKCarrier.mapResult,Option.map_map,Function.comp_def,
  qToCaller,S8OwnedP6StrictParser.limbsToActual,NKL_CanonicalKCarrier.toCaller,rawLimbs] using selected

theorem quadratic (bytes : Slice U8) (width:bytes.val.length=16) :
 NKL_CanonicalKCarrier.mapResult (Option.map qToCaller)
  (NET_ParserComposed.quadratic bytes)=ok (NKL_CanonicalKCarrier.selected bytes) := by
 rw [NET_ParserComposed.quadratic_result bytes (by omega)]
 let b : Array U8 16#usize:=⟨bytes.val,width⟩
 have same:b.to_slice=bytes := by apply Subtype.ext;rfl
 simpa only [same] using actualK b

/-- Canonical emitted child owner reused by the CLOSED NEO packet. This
adapts its result to this parent's owner without importing the old geometry
forest that redeclares Phase. Original NEO_TailReference.opening is a rfl
identity at the same reference body; no new native proof is substituted. -/
theorem opening_reference (proof : Slice U8) (i : Usize) :
 NEO_TailRef.opening proof i=NJS_Extract.verifier.candidate.opening proof i := by
 rw [NKB_CanonicalRows.opening]
 rfl

/-- The CLOSED opening helper is applied at the original proof and ordinal,
then transported to the actual emitted parent's owner. -/
theorem opening (proof : Slice U8) (width:proof.val.length=57607) (i : Usize) (bound:i.val<22) :
 ∃ q,NJS_Extract.verifier.candidate.opening proof i=ok q ∧ q.val.length=832 ∧
 MultiproofConeCanonical.bytesOf q.val=
 OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) (10055+i.val*832) 832 := by
 obtain ⟨q,read,len,bytes⟩:=Port4B_Opening.opening_exact proof width i bound
 rw [←NKB_CanonicalRows.opening] at read
 exact ⟨q,read,len,bytes⟩

set_option pp.proofs false
#print actualK
#print axioms scalar
#print axioms actualK
#print axioms quadratic
#print axioms opening_reference
#print axioms opening
end NKL_ClosedChildren
end
