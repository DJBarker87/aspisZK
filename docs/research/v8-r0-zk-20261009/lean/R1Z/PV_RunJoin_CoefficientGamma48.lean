import R1Z.PV_RunJoin_CoefficientTable48
import R1Z.PV_RunJoin_CoefficientsInstalled46
import R1Z.PV_RunJoin_GammaInstalled48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientGamma48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_CoefficientsWeight46 (Column messages)
open PV_RunJoin_BatchRowValue44 (array)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (c : Nat → Nat → Raw) (g : Raw)
    (hc : ∀ l,l<29 → ∀ j,j<1024 → canonical (c l j)) (hg : canonical g) :
    let input := fun l j => current (source (c l j))
    let gammaOps := @PV_RunJoin_GammaPowers44.inputs (types base) ops
    ∃ (coefficients : alloc.vec.Vec Column) (z : Nat → Raw) (out : alloc.vec.Vec W),
      @prover.opening_coefficients (types base) (selected base heap box gammaOps) .S2 (messages input)=ok coefficients ∧
      coefficients.length=29 ∧
      @prover.opening_batch (types base) (selected base heap box gammaOps)
        (alloc.vec.Vec.deref coefficients) (current (source g))=ok out ∧
      ProverCommitGammaOutput53.run
        (ProverCommitGammaCell53.table (fun l j => c l (AspisR1.rowNat j))) (source g)=
          ok (sourceArray 1024#usize z) ∧
      Array.to_slice (array 1024#usize z)=alloc.vec.Vec.deref out ∧
      (∀ j,j<1024 → canonical (z j)) := by
  dsimp only
  obtain ⟨coefficients,hcoeff,hv,hl⟩ := PV_RunJoin_CoefficientsInstalled46.complete base heap box
    (@PV_RunJoin_GammaPowers44.inputs (types base) ops) (fun l j => current (source (c l j)))
  obtain ⟨z,out,hbatch,hmodel,himage,hcz⟩ := PV_RunJoin_GammaInstalled48.complete base heap box ops
    (fun l j => c l (AspisR1.rowNat j)) g
    (fun l hl j _ => hc l hl _ (AspisR1.rowNat_lt j)) hg
  have table : alloc.vec.Vec.deref coefficients=
      PV_RunJoin_BatchRowValue44.table (fun l j => c l (AspisR1.rowNat j)) := by
    apply Subtype.ext
    exact hv.trans (PV_RunJoin_CoefficientTable48.complete c)
  exact ⟨coefficients,z,out,hcoeff,hl,by rw [table];exact hbatch,hmodel,himage,hcz⟩
#print axioms complete
end R1Z.PV_RunJoin_CoefficientGamma48
