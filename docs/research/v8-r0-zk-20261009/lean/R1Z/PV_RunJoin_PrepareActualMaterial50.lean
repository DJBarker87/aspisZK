import R1Z.PV_RunJoin_SemanticMaterial50
import R1Z.PV_RunJoin_PrepareMaterialContext47
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareActualMaterial50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (Weight toWeight)
open PV_RunJoin_SemanticMaterialInputs50
abbrev W := aspis_core.field.wide_exact.WideExact

def material (heap : Heap) (s : Sem) (kw : Weight) (x : W) :=
  PV_RunJoin_MaterialRun49.outcome (heap (toWeight kw) x)
    (ProverCommitWeightsMaterial53.run (ProverCommitQArray48.array 10#usize (alpha s))
      (ProverCommitNativeQ48.source (x0 s)) (ProverCommitNativeQ48.source (y0 s))
      (ProverCommitNativeQ48.source (x1 s)) (ProverCommitNativeQ48.source (y1 s))
      (ProverRwDictionaryTower.toW x))
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (backend : prover.Backend) (s : Sem) :
    ∃ kw : Weight, (toWeight kw).variant=.S2 ∧
      @prover.prepare_opening (types base) (selected base heap box ops) .S2 hash backend s=
        @PV_RunJoin_PrepareOperations47.run (types base) (selected base heap box ops) .S2 hash backend s
          (@prover.opening_coefficients (types base) (selected base heap box ops) .S2 (alloc.vec.Vec.deref backend.messages))
          (do let _ ← box .S2 s.alpha s.z;ok (.Ok (toWeight kw)))
          (fun _ x => material heap s kw x) := by
  obtain ⟨kw,hs,hctor,hmat⟩ := PV_RunJoin_SemanticMaterial50.complete base heap box ops s
  refine ⟨kw,hs,?_⟩
  rw [@PV_RunJoin_PrepareOperations47.source (types base) (selected base heap box ops) .S2 hash backend s,hctor]
  apply @PV_RunJoin_PrepareMaterialContext47.complete (types base) (selected base heap box ops)
    .S2 hash backend s _ (box .S2 s.alpha s.z) (toWeight kw)
  intro x
  have hx := hmat (ProverRwDictionaryTower.toW x)
  simpa only [ProverRwDictionaryTower.w_roundtrip,material] using hx
#print axioms material
#print axioms complete
end R1Z.PV_RunJoin_PrepareActualMaterial50
