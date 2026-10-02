import AspisR346AfterGuardsRaw
import AspisV8R19.R336PrefixPairInverseExecution
import AspisV8R19.R342OutputSetup

/-! Composition of the exact branch after the source guards. Decomposition
preserves all Results, including failures and divergence. Guard execution and
independent source-library/compiler correspondence remain separate obligations. -/
set_option autoImplicit false
namespace AspisV8R19.R350AfterGuardsExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R332PrefixInitializationSelectors
open AspisV8R19.R336PrefixPairInverseExecution
open AspisV8R19.R342OutputSetup
open AspisV8R19.R311BatchReverseLoopExecution
open AspisR335PrefixPairInverseRaw
open AspisR340BatchOutputRaw (selectedOutput0 selectedOutput1)
open AspisR346AfterGuardsRaw (selectedAfterGuards)
noncomputable section

/-- Literal source operations reassociated into existing exact fragments.
No canonical, nonempty, nonzero, capacity or success premise is required. -/
theorem after_guards_decomposition (xs ys : Slice U32) :
    selectedAfterGuards xs ys = (do
      let px ← AspisR328PrefixInitializationRaw.selectedPrefix0 xs
      let py ← selectedPrefix1 ys
      let (ix, iy) ← selectedPairInverse px py
      let ox ← selectedOutput0 xs px ix
      let oy ← selectedOutput1 ys py iy
      .ok (core.result.Result.Ok (ox, oy))) := by
  simp only [selectedAfterGuards,
    AspisR328PrefixInitializationRaw.selectedPrefix0,
    selectedPrefix1, selectedPairInverse, selectedOutput0, selectedOutput1,
    bind_assoc_eq, bind_tc_ok]

/-- The exact reverse recurrence followed by the index-zero accumulator store.
This is an output model; no success assertion is built into its definition. -/
def sourceOutput (xs : Slice U32) (f : Nat → M31Exact) (x : M31Exact) : VecU32 :=
  let m := reverseModel f (sourcePrefixValue f) (xs.val.length - 1) x (zeroVec xs)
  setNat m.2 0 (encodeBase m.1)

/-- Complete after-guards Result for canonical nonempty inputs. A zero total
retains the actual inverse assertion failure; it is not excluded by a premise. -/
theorem after_guards_complete (xs ys : Slice U32) (f g : Nat → M31Exact)
    (hx : 0 < xs.val.length) (hy : 0 < ys.val.length)
    (hf : ∀ j, j < xs.val.length → xs.val[j]? = some (encodeBase (f j)))
    (hg : ∀ j, j < ys.val.length → ys.val[j]? = some (encodeBase (g j))) :
    selectedAfterGuards xs ys =
      let p := sourcePrefixValue f (xs.val.length - 1)
      let q := sourcePrefixValue g (ys.val.length - 1)
      if p * q = 0 then .fail .assertionFailure
      else .ok (core.result.Result.Ok
        (sourceOutput xs f ((p * q)⁻¹ * q),
         sourceOutput ys g ((p * q)⁻¹ * p))) := by
  obtain ⟨px, _hxlen, hpx, hlastx, hinitx⟩ :=
    selected_prefix_initialization_bundle xs f hx hf
  obtain ⟨py, _hylen, hpy, hlasty, hinity⟩ :=
    second_prefix_bundle ys g hy hg
  rw [after_guards_decomposition, hinitx]
  simp only [bind_tc_ok]
  rw [hinity]
  simp only [bind_tc_ok]
  rw [pair_inverse_complete px py _ _ hlastx hlasty]
  dsimp only
  by_cases hz : sourcePrefixValue f (xs.val.length - 1) *
      sourcePrefixValue g (ys.val.length - 1) = 0
  · rw [if_pos hz]
    simp only [bind_tc_fail]
  · rw [if_neg hz]
    simp only [bind_tc_ok]
    rw [selectedOutput0_model xs px f (sourcePrefixValue f) _ hx
      (fun j _ hj => hf j hj)
      (fun j hj => hpx j (by omega))]
    simp only [bind_tc_ok]
    rw [selectedOutput1_model ys py g (sourcePrefixValue g) _ hy
      (fun j _ hj => hg j hj)
      (fun j hj => hpy j (by omega))]
    simp only [bind_tc_ok]
    rfl

#print axioms after_guards_decomposition
#print axioms sourceOutput
#print axioms after_guards_complete
end
end AspisV8R19.R350AfterGuardsExecution
