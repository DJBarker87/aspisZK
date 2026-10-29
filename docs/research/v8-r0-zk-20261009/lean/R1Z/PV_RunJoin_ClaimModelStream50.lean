import R1Z.PV_RunJoin_ClaimPolynomial49
import R1Z.PV_RunJoin_ClaimPolynomialStream50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimModelStream50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverRwDictionaryTower (fromW)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open PV_RunJoin_CoefficientsWeight46 (Column messages)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

attribute [local irreducible] PV_RunJoin_ClaimImageList49.stream
  PV_RunJoin_ClaimPolynomialStream50.modelCell
  ProverCommitY1Bytes47.model AspisR0.Chord.evalMessage R0P.SemSource.coeffsOf
  PV_RunJoin_ClaimPolynomial49.trace ProverCommitValueRange47.bytes

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (c : Nat → Nat → Old.Q) (hc : ∀ l,l<29 → ∀ j,j<1024 → Canonical (c l j))
    (x y : Old.Q) (hx : Canonical x) (hy : Canonical y)
    (z : AspisR0.ChordGeometry.Point ProverCommitWideOps48.Exact)
    (hzx : ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode x)=z.1.1)
    (hzy : ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode y)=z.1.2) :
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
        (PV_RunJoin_ClaimPolynomialStream50.modelCell c z) 0 29 := by
  dsimp only
  obtain ⟨coefficients,y1,hcoeff,hv,hl,hy1,h928,hstream⟩ :=
    PV_RunJoin_ClaimStream49.complete base heap box ops c hc x y hx hy
  refine ⟨coefficients,y1,hcoeff,hv,hl,hy1,h928,?_⟩
  exact hstream.trans (PV_RunJoin_ClaimPolynomialStream50.complete c x y z hzx hzy 0 29 (by omega))
#print axioms complete
end R1Z.PV_RunJoin_ClaimModelStream50
