import RPz7_S1PreparedHashErasureV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedScalarEffects
open Aeneas Aeneas.Std Result
universe v
def scalar {M : Type → Type v} [Monad M] [MonadLiftT Result M]
    (effects : PreparedHashEffects.Effects M) (B : PreparedModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool) :
  M (aspis_core.field.WideExact × (transcript.Transcript H))
  := do
  let (block, self1) ←
    PreparedHashEffects.block effects aspis_coreDigest32Inst self row payload
  let out ←
    if nonzero
    then B.gamma block
    else B.ordinary block
  let i ← lift (UScalar.cast .Usize row)
  trace.value 4#u16 i out
  pure (out, self1)

def scalar_k {M : Type → Type v} [Monad M] [MonadLiftT Result M]
    (effects : PreparedHashEffects.Effects M) (B : PreparedModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  M (aspis_core.field.QM31 × (transcript.Transcript H))
  := do
  let (a, self1) ←
    PreparedHashEffects.block effects aspis_coreDigest32Inst self row payload
  let out ← sampler.qm31_sample a
  let i ← lift (UScalar.cast .Usize row)
  let we ← B.fromQm out
  trace.value 4#u16 i we
  pure (out, self1)

theorem scalar_source (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) (nonzero : Bool) :
    scalar PreparedHashEffects.sourceEffects B D self row payload nonzero=
      PreparedModel.scalar B D self row payload nonzero := by cases nonzero <;> rfl

theorem scalar_k_source (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    scalar_k PreparedHashEffects.sourceEffects B D self row payload=
      PreparedModel.scalar_k B D self row payload := rfl

#print axioms scalar_source
#print axioms scalar_k_source
end AspisR1PublicPreparation.PreparedScalarEffects
