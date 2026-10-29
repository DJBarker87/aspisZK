import R1Z.PV_RunJoin_BatchInstalled48
import R1Z.PV_RunJoin_GammaAssociation44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaInstalled48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_BatchRowValue44 (table array)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

/-- Complete source law with the exact powers-source installation explicit.
No claim about the deployed caller's incoming dictionary is implicit. -/
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (c : Nat → Nat → Raw) (g : Raw)
    (hc : ∀ l,l<29 → ∀ j,j<1024 → canonical (c l j)) (hg : canonical g) :
    ∃ (z : Nat → Raw) (out : alloc.vec.Vec W),
      @prover.opening_batch (types base)
        (selected base heap box (@PV_RunJoin_GammaPowers44.inputs (types base) ops))
        (table c) (current (source g))=ok out ∧
      ProverCommitGammaOutput53.run (ProverCommitGammaCell53.table c) (source g)=ok (sourceArray 1024#usize z) ∧
      Array.to_slice (array 1024#usize z)=alloc.vec.Vec.deref out ∧
      (∀ j,j<1024 → canonical (z j)) := by
  obtain ⟨z,out,hcur,hmodel,himage,hcz⟩ := @PV_RunJoin_GammaAssociation44.complete (types base) ops c g hc hg
  refine ⟨z,out,?_,hmodel,himage,hcz⟩
  rw [PV_RunJoin_BatchInstalled48.complete base heap box _]
  exact hcur
#print axioms complete
end R1Z.PV_RunJoin_GammaInstalled48
