import ExtractedTx1Model

/-! Obstruction at the retained tx1 boundary, not a model of checkpoint
serialization. The accepted extraction permits arbitrary finish results. -/
set_option autoImplicit false
namespace AspisR1PublicPreparation.Tx1CheckpointBoundary
open Aeneas Aeneas.Std Result

/-- The accepted boundary record can be instantiated with any output bytes.
Consequently its signature alone establishes neither a checkpoint length nor
a digest field nor the zero-account rule. -/
def withOutput (B : Tx1Model.Boundaries) (out : alloc.vec.Vec U8) :
    Tx1Model.Boundaries :=
  { B with finish := fun {_} _ _ _ _ _ _ _ _ _ _ => ok (.Ok out) }

theorem arbitrary_finish_output (B : Tx1Model.Boundaries)
    {Hash : Type} (D : aspis_core.Digest32 Hash) (v : verifier.View)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.WideExact 29#usize)
    (publicBytes proof : Slice U8) (k : Usize) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit)) (out : alloc.vec.Vec U8) :
    (withOutput B out).finish D v p a g publicBytes proof k hash obs = ok (.Ok out) := rfl

/-- A concrete countermodel schema to uniqueness across unconstrained accepted
tail implementations: identical arguments can return different byte vectors.
This does not allege a counterexample to the actual Rust writer. -/
theorem distinct_finish_outputs (B : Tx1Model.Boundaries)
    {Hash : Type} (D : aspis_core.Digest32 Hash) (v : verifier.View)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.WideExact 29#usize)
    (publicBytes proof : Slice U8) (k : Usize) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit))
    (x y : alloc.vec.Vec U8) (hne : x ≠ y) :
    (withOutput B x).finish D v p a g publicBytes proof k hash obs ≠
      (withOutput B y).finish D v p a g publicBytes proof k hash obs := by
  intro h
  exact hne (core.result.Result.Ok.inj (Result.ok.inj h))

#print axioms arbitrary_finish_output
#print axioms distinct_finish_outputs
end AspisR1PublicPreparation.Tx1CheckpointBoundary
