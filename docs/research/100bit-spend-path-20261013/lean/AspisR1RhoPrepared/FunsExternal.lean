import AspisR1RhoPrepared.Types
import AspisR1RhoScalarK.Funs

/-! Common unchanged preparation calls are arbitrary computations, with no
success or canonicality law assumed. The scalar_k call is the actual checked
source function, with coordinate-only transport of its QM31 result. -/
set_option autoImplicit false
namespace AspisR1RhoPowerTail
open Aeneas Aeneas.Std Result

class PreparedCommon where
  toBytes : aspis_core.field.WideExact → Result (Array U8 32#usize)
  state : {H : Type} → aspis_core.Digest32 H → r1_wire.SemanticTranscript H → Result (Array U8 32#usize)
  newTranscript : {H : Type} → aspis_core.Digest32 H → H → Array U8 32#usize → transport.Variant → Result (transcript.Transcript H)
  scalar : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 → Bool →
    Result (aspis_core.field.WideExact × transcript.Transcript H)
  queries : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 →
    Result ((core.result.Result (Array U32 22#usize) verifier.Error) × transcript.Transcript H)
  powers : (N : Usize) → aspis_core.field.WideExact → Result (Array aspis_core.field.WideExact N)
  claim : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 →
    aspis_core.field.WideExact → Array aspis_core.field.WideExact 29#usize → aspis_core.field.WideExact →
    Result (core.result.Result aspis_core.field.WideExact verifier.Error)

abbrev aspis_core.field.WideExact.to_le_bytes [PreparedCommon] := PreparedCommon.toBytes
abbrev r1_wire.SemanticTranscript.impl.state [PreparedCommon] := @PreparedCommon.state _
abbrev transcript.Transcript.new [PreparedCommon] := @PreparedCommon.newTranscript _
abbrev transcript.Transcript.scalar [PreparedCommon] := @PreparedCommon.scalar _
abbrev transcript.Transcript.queries [PreparedCommon] := @PreparedCommon.queries _
abbrev weights.powers [PreparedCommon] := PreparedCommon.powers
abbrev gamma_new.prepared_claim [PreparedCommon] := @PreparedCommon.claim _

def fromRhoSource (q : AspisR1CuRho.field.QM31) : aspis_core.field.QM31 :=
  {c0:={a:=q.c0.a,b:=q.c0.b},c1:={a:=q.c1.a,b:=q.c1.b}}

def toRhoSource (q : aspis_core.field.QM31) : AspisR1CuRho.field.QM31 :=
  {c0:={a:=q.c0.a,b:=q.c0.b},c1:={a:=q.c1.a,b:=q.c1.b}}

def transcript.Transcript.scalar_k [AspisR1CuRho.ScalarKBlocks] {H : Type}
    (D : aspis_core.Digest32 H) (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    Result (aspis_core.field.QM31 × transcript.Transcript H) := do
  let (q,after) ← AspisR1CuRho.transcript.Transcript.scalar_k D self row payload
  .ok (fromRhoSource q,after)

#print axioms PreparedCommon
#print axioms transcript.Transcript.scalar_k
end AspisR1RhoPowerTail
