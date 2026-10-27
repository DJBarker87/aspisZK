import XSa_PointRun
open Aeneas Aeneas.Std Result ControlFlow
open XRo_Join_Carriers XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_PointBody
open AspisR1ClaimPreparedBridge

theorem body {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (k parts : XRy_ClaimSumStep.Seven)
 (iter iter' : Range)
 (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some iter.start,iter')) :
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body ops D (toClaimSem sem) s
   (arr toClaimE g) (arr toClaimE k) iter (arr toClaimE parts) =
 (do
   let r ← AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot ops D (toClaimSem sem) s (arr toClaimE g) iter.start
   let cf ← core.result.Result.Insts.CoreOpsTry.branch r
   match cf with
   | core.ops.control_flow.ControlFlow.Continue val => do
     let j ← iter.start+1#usize
     let out ← Array.update (arr toClaimE parts) j val
     ok (.cont (iter',out))
   | core.ops.control_flow.ControlFlow.Break residual => do
     let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       AspisR1CurrentPreparedClaim.Concrete.E (core.convert.FromSame AspisR1CurrentPreparedClaim.verifier.Error) residual
     ok (.done r1)) := by
 unfold AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body
 rw [hn,bind_tc_ok]
 rfl

#print axioms body
end XSa_PointBody
