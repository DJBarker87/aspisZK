import R1Z.PV_RunJoin_ClaimEvaluation49
import R1Z.PV_RunJoin_CoefficientTable48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimColumn49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)

theorem column (p : Nat → Old.Q) :
    PV_RunJoin_CoefficientsWeight46.column (fun j => fromW (ProverCommitNativeOps47.embedded (p j)))=
      amap fromW (ProverCommitPairCounter47.sourceArray 1024#usize (fun j => p (AspisR1.rowNat j))) := by
  apply Subtype.ext
  simp only [PV_RunJoin_CoefficientsWeight46.column,ProverCommitArray49.array,
    amap,ProverCommitPairCounter47.sourceArray,List.map_ofFn]

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (p : Nat → Old.Q) (hp : ∀ j,j<1024 → Canonical (p j))
    (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q,
      PV_RunJoin_ClaimProducerCell48.evaluate base heap box (@PV_DL_EncoderSelected.selected (types base) ops)
        ⟨fromW (ProverCommitNativeOps47.embedded x),fromW (ProverCommitNativeOps47.embedded y)⟩
        (PV_RunJoin_CoefficientsWeight46.column (fun j => fromW (ProverCommitNativeOps47.embedded (p j))))=
          ok (fromW (ProverCommitNativeOps47.embedded z)) ∧
      Canonical z ∧ decode z=ProverCommitEval47.messageEval
        (fun j : Fin 1024 => decode (p (AspisR1.rowNat j.val))) (decode x) (decode y) := by
  rw [column]
  exact PV_RunJoin_ClaimEvaluation49.subfield base heap box ops (fun j => p (AspisR1.rowNat j))
    (fun j _ => hp _ (AspisR1.rowNat_lt j)) x y hx hy
#print axioms column
#print axioms complete
end R1Z.PV_RunJoin_ClaimColumn49
