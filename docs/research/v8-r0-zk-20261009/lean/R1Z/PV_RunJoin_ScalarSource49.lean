import R1Z.PV_RunJoin_SamplerValue49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ScalarSource49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48

def retained (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (self : host_transcript.Transcript H)
    (row : U8) (payload : Slice U8) (nonzero : Bool) : Result (aspis_core.field.wide_exact.WideExact × host_transcript.Transcript H) := do
  let (block,next) ← @host_transcript.Transcript.block (types base) (selected base heap box ops) H D self row payload
  let a := PV_RunJoin_SamplerValue49.value base heap box ops block nonzero
  let i ← Aeneas.Std.lift (UScalar.cast .Usize row)
  let _ ← @trace.value (types base) (selected base heap box ops) 4#u16 i (ProverRwDictionaryTower.fromW (source a))
  ok (ProverRwDictionaryTower.fromW (source a),next)

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (self : host_transcript.Transcript H)
    (row : U8) (payload : Slice U8) (nonzero : Bool) :
    @host_transcript.Transcript.scalar (types base) (selected base heap box ops) H D self row payload nonzero=
      retained base heap box ops D self row payload nonzero := by
  unfold host_transcript.Transcript.scalar retained
  apply congrArg (Aeneas.Std.bind _)
  funext pair
  rcases pair with ⟨block,next⟩
  dsimp only [Aeneas.Std.uncurry]
  rw [(PV_RunJoin_SamplerValue49.spec base heap box ops block nonzero).1]
  rfl
#print axioms retained
#print axioms complete
end R1Z.PV_RunJoin_ScalarSource49
