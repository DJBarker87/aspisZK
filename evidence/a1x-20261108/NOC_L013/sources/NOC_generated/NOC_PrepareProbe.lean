import NOC_Run5bHost
import NNH_SliceRangeOk
import NNV_PreparedFront
import NNV_PrepareView
import NNV_PrepareValuesOutput
import NNV_PrepareSemanticOutput
import NNV_PrepareBufferLengths
import NNV_PrepareFilled
import NNH_Run5bCurrentExpand
import NNH_Run5bCurrentValues
set_option autoImplicit false
open Lean Meta Elab Command
/-- Diagnostic only: theorems available in this closure that mention the
prepare-front buffer primitives, and selected definitions. -/
run_cmd do
  let env ← getEnv
  let targets : List Name := [`AspisS1ValuesOwnedInstallation.expandValues, `alloc.vec.Vec.index,
    `Aeneas.Std.alloc.vec.Vec.index, `Aeneas.Std.core.slice.Slice.split_at_mut,
    `Aeneas.Std.alloc.vec.Vec.deref_mut, `AspisS1ValuesOwned.values_owned_reference,
    `NFU_Retarget.compact.expand_values]
  let mut n := 0
  for (nm, ci) in env.constants.toList do
    if ci.isTheorem && n < 120 then
      let ty := ci.type
      if targets.any (fun t => (ty.find? (fun e => e.isConstOf t)).isSome) then
        n := n + 1
        logInfo m!"THM {nm} : {ty}"
  for t in [`Aeneas.Std.alloc.vec.Vec.deref_mut, `Aeneas.Std.core.slice.Slice.split_at_mut,
      `Aeneas.Std.alloc.vec.Vec.index, `AspisS1ValuesOwnedInstallation.toVec,
      `AspisS1ValuesOwnedInstallation.toSlice, `AspisR1.NNH_ResultWp.expose, `NNH_ResultWp.expose] do
    match env.find? t with
    | some ci => logInfo m!"DEF {t} : {ci.type} := {ci.value?.getD (mkConst `none)}"
    | none => logInfo m!"DEF {t} unknown"
#check @NNH_SliceRangeOk.value
#check @AspisR1.NNV_PrepareView.returned
#check @AspisR1.NNH_Run5bCurrentExpand.semantic
