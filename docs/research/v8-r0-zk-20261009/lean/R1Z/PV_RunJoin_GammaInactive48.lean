import R1Z.PV_RunJoin_CoefficientGamma48
import R1Z.PV_RunJoin_InactiveInstalled48
import R1Z.PV_RunJoin_InactiveModel48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaInactive48
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
    (hc : ∀ l,l<29 → ∀ j,j<1024 → canonical (c l j)) (hg : canonical g)
    (w : PV_RunJoin_WeightCarrier46.W) (hs : w.variant=.S2)
    (ch : R0Z.HonestView.Challenges Exact) :
    let gammaOps := @PV_RunJoin_GammaPowers44.inputs (types base) ops
    ∃ (coefficients : alloc.vec.Vec Column) (q : Nat → Raw) (out : alloc.vec.Vec W) (s : Raw),
      @prover.opening_coefficients (types base) (selected base heap box gammaOps) .S2
        (messages (fun l j => current (source (c l j))))=ok coefficients ∧
      @prover.opening_batch (types base) (selected base heap box gammaOps)
        (alloc.vec.Vec.deref coefficients) (current (source g))=ok out ∧
      @prover.opening_inactive (types base) (selected base heap box gammaOps)
        (alloc.vec.Vec.deref out) w=ok (current (source s)) ∧
      canonical s ∧ value s=R1Z.Batched.ell AspisR1.rowEquiv ch 0 (fun i => value (q i.val)) ∧
      ProverCommitGammaOutput53.run (ProverCommitGammaCell53.table (fun l j => c l (AspisR1.rowNat j))) (source g)=
        ok (sourceArray 1024#usize q) := by
  dsimp only
  obtain ⟨coefficients,q,out,hcfs,hl,hbatch,hmodel,himage,hcq⟩ :=
    PV_RunJoin_CoefficientGamma48.complete base heap box ops c g hc hg
  obtain ⟨s,hinactive,hcs,hvalue,hbytes⟩ := PV_RunJoin_InactiveInstalled48.complete base heap box
    (@PV_RunJoin_GammaPowers44.inputs (types base) ops) q hcq w hs
  have input : PV_RunJoin_InactiveValueCell48.input q=alloc.vec.Vec.deref out := himage
  refine ⟨coefficients,q,out,s,hcfs,hbatch,?_,hcs,?_,hmodel⟩
  · rw [←input]
    exact hinactive
  · rw [hvalue,PV_RunJoin_InactiveModel48.complete q ch]
#print axioms complete
end R1Z.PV_RunJoin_GammaInactive48
