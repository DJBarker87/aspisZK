import AspisR1CuGamma.Types

/-! Explicit universal source boundaries, no imported axiom template.
Old/new claim helpers remain separate parameters: no unproved claim-suffix
equivalence is hidden in this interpretation. -/
set_option autoImplicit false
namespace AspisR1CuGamma
open Aeneas Aeneas.Std Result

class Boundaries where
  toBytes : aspis_core.field.WideExact → Result (Array U8 32#usize)
  state : {H : Type} → aspis_core.Digest32 H → r1_wire.SemanticTranscript H → Result (Array U8 32#usize)
  newTranscript : {H : Type} → aspis_core.Digest32 H → H → Array U8 32#usize → transport.Variant → Result (transcript.Transcript H)
  scalar : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 → Bool →
    Result (aspis_core.field.WideExact × transcript.Transcript H)
  scalarK : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 →
    Result (aspis_core.field.QM31 × transcript.Transcript H)
  queries : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 →
    Result ((core.result.Result (Array U32 22#usize) verifier.Error) × transcript.Transcript H)
  powers : (N : Usize) → aspis_core.field.WideExact → Result (Array aspis_core.field.WideExact N)
  oldClaim : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 →
    aspis_core.field.WideExact → aspis_core.field.WideExact → aspis_core.field.WideExact →
    Result (core.result.Result aspis_core.field.WideExact verifier.Error)
  newClaim : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 →
    aspis_core.field.WideExact → Array aspis_core.field.WideExact 29#usize → aspis_core.field.WideExact →
    Result (core.result.Result aspis_core.field.WideExact verifier.Error)

abbrev aspis_core.field.WideExact.to_le_bytes [Boundaries] := Boundaries.toBytes
abbrev r1_wire.SemanticTranscript.impl.state [Boundaries] := @Boundaries.state _
abbrev transcript.Transcript.new [Boundaries] := @Boundaries.newTranscript _
abbrev transcript.Transcript.scalar [Boundaries] := @Boundaries.scalar _
abbrev transcript.Transcript.scalar_k [Boundaries] := @Boundaries.scalarK _
abbrev transcript.Transcript.queries [Boundaries] := @Boundaries.queries _
abbrev weights.powers [Boundaries] := Boundaries.powers
abbrev gamma_old.prepared_claim [Boundaries] := @Boundaries.oldClaim _
abbrev gamma_new.prepared_claim [Boundaries] := @Boundaries.newClaim _

#print axioms Boundaries
#print axioms gamma_old.prepared_claim
#print axioms gamma_new.prepared_claim
#print axioms weights.powers
end AspisR1CuGamma
