import R1Z.PV_RunJoin_ClaimBytes49
import R1Z.PV_RunJoin_ClaimStreamImage49
import R1Z.PV_RunJoin_ClaimLength48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimStream49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverRwDictionaryTower (fromW)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open PV_RunJoin_CoefficientsWeight46 (Column messages)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (c : Nat → Nat → Old.Q) (hc : ∀ l,l<29 → ∀ j,j<1024 → Canonical (c l j))
    (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    let encOps := @PV_DL_EncoderSelected.selected (types base) ops
    ∃ (coefficients : alloc.vec.Vec Column) (y1 : alloc.vec.Vec U8),
      @prover.opening_coefficients (types base) (selected base heap box encOps) .S2
        (messages (fun l j => fromW (ProverCommitNativeOps47.embedded (c l j))))=ok coefficients ∧
      coefficients.val=PV_RunJoin_CoefficientsWeight46.payload
        (fun l j => fromW (ProverCommitNativeOps47.embedded (c l j))) 0 29 ∧
      coefficients.length=29 ∧
      @prover.opening_claim_bytes (types base) (selected base heap box encOps) (alloc.vec.Vec.deref coefficients)
        ⟨fromW (ProverCommitNativeOps47.embedded x),fromW (ProverCommitNativeOps47.embedded y)⟩=ok y1 ∧
      y1.length=928 ∧
      y1.val.map PV_RunJoin_WideImage43.byte=PV_RunJoin_ClaimImageList49.stream
        (fun l => List.ofFn (ProverCommitValueRange47.bytes
          (ProverCommitY1Bytes47.model (fun j => c l (AspisR1.rowNat j)) x y))) 0 29 := by
  dsimp only
  obtain ⟨coefficients,y1,z,hcoeff,hv,hl,hy1,hyv,hcz,hdz⟩ :=
    PV_RunJoin_ClaimBytes49.complete base heap box ops c hc x y hx hy
  refine ⟨coefficients,y1,hcoeff,hv,hl,hy1,?_,?_⟩
  · change y1.val.length=928
    rw [hyv,PV_RunJoin_ClaimImage48.length,List.length_ofFn]
  · rw [hyv]
    exact PV_RunJoin_ClaimStreamImage49.complete c x y z hcz hdz
#print axioms complete
end R1Z.PV_RunJoin_ClaimStream49
