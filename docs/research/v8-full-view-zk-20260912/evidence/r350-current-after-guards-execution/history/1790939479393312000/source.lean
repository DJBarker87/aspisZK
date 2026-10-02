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
open AspisR340BatchOutputRaw (selectedOutput0 selectedOutput1 VecU32)
open AspisR346AfterGuardsRaw (selectedAfterGuards)
noncomputable section

/-- Literal source operations reassociated into existing exact fragments.
No canonical, nonempty, nonzero, capacity or success premise is required. -/
theorem after_guards_decomposition (xs ys : Slice U32) :
    selectedAfterGuards xs ys = do
      let px ← AspisR328PrefixInitializationRaw.selectedPrefix0 xs
      let py ← selectedPrefix1 ys
      let (ix, iy) ← selectedPairInverse px py
      let ox ← selectedOutput0 xs px ix
      let oy ← selectedOutput1 ys py iy
      .ok (core.result.Result.Ok (ox, oy)) := by
  simp only [selectedAfterGuards,
    AspisR328PrefixInitializationRaw.selectedPrefix0,
    selectedPrefix1, selectedPairInverse, selectedOutput0, selectedOutput1,
    bind_assoc_eq, bind_tc_ok]

#print axioms after_guards_decomposition
end
end AspisV8R19.R350AfterGuardsExecution
