import XSf_Nonvacuity
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSf_ParserWitness

def zeroBytes : Array U8 32#usize := Array.repeat 32#usize 0#u8

theorem parsed_zero : _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes
 (Array.to_slice zeroBytes)=ok (some XRy_Powers.zero) := by
 rw [XSa_ParserFixed.fixed]
 have h : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice zeroBytes)=
   ok (some (AspisR1.ExtractedRecordLimbCanonicality.packed 0#u32 0#u32 0#u32 0#u32 0#u32 0#u32 0#u32 0#u32)) := by
   rw [AspisR1.ExtractedRecordByteCanonicality.fixed_reads]
   rfl
 rw [h]
 rfl

theorem parse_inhabited : ∃ s : Slice U8, ∃ x : C.E,
 _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes s=ok (some x) ∧
 XRy_WideMultiply.Canonical x :=
 ⟨Array.to_slice zeroBytes,XRy_Powers.zero,parsed_zero,XRy_ClaimSum.zero_canonical⟩

/-- Serialization alone does not imply canonicality of an arbitrary typed
view. The public A2 theorem derives bounds from its parser instead. -/
theorem serializer_counterexample : ∃ x : C.E, ∃ b : Array U8 32#usize,
 XRo_Join_Installed.actual.sampling.toBytes x=ok b ∧ ¬XRy_WideMultiply.Canonical x := by
 let x : C.E := ⟨⟨⟨2147483647#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,
   ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
 refine ⟨x,AspisR1CurrentCaller.OriginalSerializerInstallation.expectedBytes x,
   AspisR1CurrentCaller.OriginalSerializerInstallation.sourceBytes_total x,?_⟩
 intro hc
 have impossible := hc.1.1.1
 change 2147483647<2147483647 at impossible
 omega

#print axioms parsed_zero
#print axioms parse_inhabited
#print axioms serializer_counterexample
end XSf_ParserWitness
