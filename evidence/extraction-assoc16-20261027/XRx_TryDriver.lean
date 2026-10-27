import XRx_TryChain
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRx_TryDriver
/-- The generated Try spelling of the same n-stage driver. -/
def run {E S : Type} (step : Nat → S → Result (core.result.Result S E)) :
 Nat → Nat → S → Result (core.result.Result S E)
 | _,0,s => ok (.Ok s)
 | i,n+1,s => do
  let r ← step i s
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue next => run step (i+1) n next
  | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    S (core.convert.FromSame E) residual

theorem source {E S : Type} (step : Nat → S → Result (core.result.Result S E))
 (n i : Nat) (s : S) : run step i n s=
 XRx_StageFold.fold step (List.range' i n) (.Ok s) := by
 rw [←XRx_StageFold.source]
 induction n generalizing i s with
 | zero => rfl
 | succ n ih =>
  rw [run,XRx_StageRules.next]
  unfold XRx_StageRules.chain
  cases h : step i s with
  | fail e => rfl
  | div => rfl
  | ok r =>
   cases r with
   | Err e => rfl
   | Ok next => simpa only [bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch] using ih (i+1) next
#print axioms source
end XRx_TryDriver
