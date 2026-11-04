import NFJ_Comparison
set_option autoImplicit false
noncomputable section
namespace NFJ_Scanner
open Aeneas Aeneas.Std Result

/-- Mathematical execution model; completion is used only off the native
688-byte call domain. RuntimeMemcmp(ac) is explicitly retained as ADDED trust. -/
def run (reply : List U8 → List U8 → Int) (bytes : Slice U8) :=
  NFD_ScanConditional.run (NFH_ComparisonDomain.complete688 reply) bytes

/-- Scanner root MODEL theorem. Native forwarding and CLOSED callee packets
supply the separate ruling-(y) hybrid source link. No inner callee bridge,
PacketDomain or PhysicalInterpretation hypothesis is introduced here. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State)
    (reply : List U8 → List U8 → Int)
    (runtimeMemcmp : NFJ_Comparison.RuntimeMemcmp reply) :
    (run reply bytes,state,([] : List Unit)) =
    (AspisR1.JHf_Scan.source bytes,state,[]) :=
  NFD_ScanConditional.result_state_effects bytes state _
    (NFJ_Comparison.completion reply runtimeMemcmp)

/-- The successful encode carrier, including arbitrary error replies before
it is reached, has exactly the native fixed-array width. -/
theorem encode_domain (encoded : Array U8 688#usize) :
    encoded.to_slice.val.length = 688 := encoded.property

/-- Same reached decode range: no independent bytes or success witness. -/
theorem decode_domain (bytes : List U8) (length : bytes.length = 58295) :
    (NFJ_Comparison.header bytes).length = 688 :=
  NFJ_Comparison.header_length bytes length

/-- The only tag call is S2; the adopted source continuation tests byte696
against2. The native callsite uses the CLOSED Variant::tag packet. -/
theorem tag_domain (tag : U8) :
    (tag != 2#u8) = false ↔ tag = 2#u8 := by
  simp only [Bool.not_eq_true, bne_iff_ne, ne_eq, not_not]

#print axioms result_state_effects
#print axioms encode_domain
#print axioms decode_domain
#print axioms tag_domain
end NFJ_Scanner
