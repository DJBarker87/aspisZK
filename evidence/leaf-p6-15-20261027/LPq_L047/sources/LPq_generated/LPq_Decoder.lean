import LPq_Powers
import XRo_Join_ResultTransport
set_option autoImplicit false
namespace AspisR1.LPq_Decoder
open Aeneas Aeneas.Std Result LPi_FieldValues XRo_Join_Carriers XRo_Join_ResultTransport

def record (x : NE) : AspisR1RecordParser.field.wide_exact.WideExact :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem limbs (a : Array U32 8#usize) :
    mapR (Option.map record) (FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs a)=
      AspisR1RecordParser.field.wide_exact.WideExact.from_limbs a := by
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
    AspisR1RecordParser.field.wide_exact.WideExact.from_limbs,
    FIo_Native.aspis_core.field.P,AspisR1RecordParser.field.P,
    mapR_bind,map_if,map_ok,Option.map_some,Option.map_none,record]

theorem bytes (b : Slice U8) :
    mapR (Option.map record) (FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes b)=
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes b := by
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes,
    FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,
    AspisR1RecordParser.field.wide_exact.WideExact.BYTE_LEN,
    map_if,map_ok,Option.map_none,mapR_bind,limbs]

theorem unwrap (o : Option NE) :
    mapR record (core.option.Option.unwrap o)=core.option.Option.unwrap (Option.map record o) := by
  cases o <;> rfl

theorem field (b : Slice U8) (i : Usize) :
    mapR record (FIo_Native.weights.field b i)=
      AspisR1WeightsFieldCurrent.weights.field
        AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes b i := by
  unfold FIo_Native.weights.field AspisR1WeightsFieldCurrent.weights.field
  simp only [mapR_bind,←bytes,bind_map,unwrap]

/-- SAME selected-byte parser, full Result including noncanonical and range
failures, after the concrete eight-word cohort owner port. -/
theorem claim_field (b : Slice U8) (i : Usize) :
    mapR LPq_Powers.claim (FIo_Native.weights.field b i)=
      AspisR1CurrentPreparedClaim.ClaimParser.field b i := by
  unfold AspisR1CurrentPreparedClaim.ClaimParser.field AspisR1CurrentWide.Proof.finishField
  rw [←field]
  simp only [mapR,bind_assoc_eq,bind_tc_ok]
  rfl

#print axioms limbs
#print axioms bytes
#print axioms unwrap
#print axioms field
#print axioms claim_field
end AspisR1.LPq_Decoder
