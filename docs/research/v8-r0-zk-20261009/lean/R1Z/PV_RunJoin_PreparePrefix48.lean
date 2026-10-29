import R1Z.PV_RunJoin_PrepareClaimCongruence48
import R1Z.PV_RunJoin_ClaimVector48
import R1Z.PV_RunJoin_InactiveRun48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PreparePrefix48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_PrepareClaimCongruence48 (W Column Material)
open PV_RunJoin_WeightMap46 (mapResult)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (coefficients : alloc.vec.Vec Column) (small : coefficients.length≤14336)
    (request : Result Unit) (w : PV_RunJoin_WeightCarrier46.W) (hs : w.variant=.S2)
    (material : weights.Weights → W → Result (core.result.Result (alloc.vec.Vec W) verifier.Error)) :
    @PV_RunJoin_PrepareOperations47.run (types base) (selected base heap box ops)
      .S2 hash backend sem (ok coefficients) (do let _ ← request;ok (.Ok w)) material=
    @PV_RunJoin_PrepareClaimContext48.run (types base) (selected base heap box ops)
      .S2 hash backend sem (ok coefficients) (do let _ ← request;ok (.Ok w)) material
      (fun columns point => PV_RunJoin_ClaimProducer48.run
        (PV_RunJoin_ClaimProducerCell48.evaluate base heap box ops point) columns.val (alloc.vec.Vec.new U8))
      (fun q _ => mapResult ProverRwDictionaryTower.fromW
        (PV_RunJoin_InactiveFinite48.run 1024 q (PV_RunJoin_WeightCarrier46.state w)
          AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO 0#usize)) := by
  rw [@PV_RunJoin_PrepareClaimContext48.source (types base) (selected base heap box ops)
    .S2 hash backend sem (ok coefficients) (do let _ ← request;ok (.Ok w)) material]
  trans @PV_RunJoin_PrepareClaimContext48.run (types base) (selected base heap box ops)
    .S2 hash backend sem (ok coefficients) (do let _ ← request;ok (.Ok w)) material
    (fun columns point => PV_RunJoin_ClaimProducer48.run
      (PV_RunJoin_ClaimProducerCell48.evaluate base heap box ops point) columns.val (alloc.vec.Vec.new U8))
    (@prover.opening_inactive (types base) (selected base heap box ops))
  · apply @PV_RunJoin_PrepareClaimCongruence48.claim (types base) (selected base heap box ops)
      .S2 hash backend sem coefficients _ material _ _ _
    intro point
    exact PV_RunJoin_ClaimVector48.complete base heap box ops (alloc.vec.Vec.deref coefficients) point small
  · apply @PV_RunJoin_PrepareClaimCongruence48.inactive (types base) (selected base heap box ops)
      .S2 hash backend sem (ok coefficients) request w material _ _ _
    intro q
    exact PV_RunJoin_InactiveRun48.complete base heap box ops q w hs
#print axioms complete
end R1Z.PV_RunJoin_PreparePrefix48
