import NHT_COMBINED_IMPORT
import NHV_NEB_ArrayRefs
import NHV_NBG_WideCarriers
import NHV_NBG_WideBytes
import NBG_Atomic
import NEB_PureFrame

set_option autoImplicit false
namespace NEO_ParserShapes
open Aeneas Aeneas.Std Result AspisR1
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact

/-- The public observation used by the native parser harness is lossless on
all raw WideExact carriers, including noncanonical records. -/
theorem wide_observation_injective (x y : E)
    (same : FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x =
      FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs y) : x = y := by
  apply NEB_ArrayRefs.wide_injective
  exact Result.ok.inj same

/-- The same eight raw limbs give the exact parser Result, canonicality test,
and pure frame. There is no precondition that the parser accepts. -/
theorem limbs_result {S Event : Type} (state : S) (a b c d e f g h : U32) :
    NEB_PureFrame.run (Event:=Event) state
      (FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
        (Array.make 8#usize [a,b,c,d,e,f,g,h])) =
      ok ((if a < 2147483647#u32 ∧ b < 2147483647#u32 ∧ c < 2147483647#u32 ∧
        d < 2147483647#u32 ∧ e < 2147483647#u32 ∧ f < 2147483647#u32 ∧
        g < 2147483647#u32 ∧ h < 2147483647#u32
        then some (LPf_WideConstruction.value a b c d e f g h) else none),state,[]) := by
  exact NEB_PureFrame.successful state _ _ (NBG_WideCarriers.limbs_result a b c d e f g h)

/-- All fixed four-byte encodings, with exact rejection and no canonical-input
premise. The value is the actual standard little-endian primitive. -/
theorem scalar_result {S Event : Type} (state : S) (bytes : Array U8 4#usize) :
    NEB_PureFrame.run (Event:=Event) state
      (AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes bytes) =
    ok ((let word := core.num.U32.from_le_bytes bytes
      if word >= 2147483647#u32 then none else some word),state,[]) := by
  exact NEB_PureFrame.successful state _ _ (NBG_Atomic.m31_decode bytes)

#print axioms wide_observation_injective
#print axioms limbs_result
#print axioms scalar_result
end NEO_ParserShapes
