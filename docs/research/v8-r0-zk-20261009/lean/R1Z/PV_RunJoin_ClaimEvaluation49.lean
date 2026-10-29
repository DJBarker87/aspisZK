import R1Z.PV_RunJoin_EncoderInstalled49
import R1Z.PV_RunJoin_ClaimEvaluator48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimEvaluation49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderCell49 (S)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (q : Array S 1024#usize) (x y : S) :
    PV_RunJoin_ClaimProducerCell48.evaluate base heap box (@PV_DL_EncoderSelected.selected (types base) ops)
      ⟨fromW x,fromW y⟩ (amap fromW q)=mapResult fromW (PV_RunJoin_EncoderValue49.run q x y) := by
  rw [PV_RunJoin_ClaimEvaluator48.complete]
  exact PV_RunJoin_EncoderInstalled49.complete base heap box _ q x y

theorem subfield (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (q : Nat → Old.Q) (hq : ∀ j,j<1024 → Canonical (q j))
    (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q,
      PV_RunJoin_ClaimProducerCell48.evaluate base heap box (@PV_DL_EncoderSelected.selected (types base) ops)
        ⟨fromW (ProverCommitNativeOps47.embedded x),fromW (ProverCommitNativeOps47.embedded y)⟩
        (amap fromW (ProverCommitPairCounter47.sourceArray 1024#usize q))=
          ok (fromW (ProverCommitNativeOps47.embedded z)) ∧
      Canonical z ∧ decode z=ProverCommitEval47.messageEval
        (fun j : Fin 1024 => decode (q j.val)) (decode x) (decode y) := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitY1Owner47.value q hq x y hx hy
  refine ⟨z,?_,hcz,hdz⟩
  rw [complete]
  have hrun : PV_RunJoin_EncoderValue49.run (ProverCommitPairCounter47.sourceArray 1024#usize q)
      (ProverCommitNativeOps47.embedded x) (ProverCommitNativeOps47.embedded y)=ProverCommitY1Owner47.run q x y :=
    ProverCommitNativeEval48.run_owner q x y
  rw [hrun,hz]
  rfl
#print axioms complete
#print axioms subfield
end R1Z.PV_RunJoin_ClaimEvaluation49
