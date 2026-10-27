import XSa_DotDone
open Aeneas Aeneas.Std Result ControlFlow
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_DotBody
open AspisR1ClaimPreparedBridge

theorem body {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (hg : canonical g)
 (point : Nat) (hp : point<6) (iter iter' : Range) (hi : iter.start.val<29)
 (a b : Dot)
 (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some iter.start,iter')) :
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot_loop.body ops D s (arr toClaimE g)
   iter (toClaimSem sem) (XRn_Join_usize point) (state a b iter.start) =
 (do
   let q ← XRy_ClaimSelect.read (es sem) s point iter.start.val
   let (r,dot1) ← ops.pushDot (state a b iter.start) (toClaimE (cell g iter.start hi)) (toClaimQ (cq q))
   let r1 ← AspisR1CurrentPreparedClaim.core.result.Result.map_err
     (AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError D) r ()
   let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
   match cf with
   | core.ops.control_flow.ControlFlow.Continue _ => ok (.cont (iter',toClaimSem sem,XRn_Join_usize point,dot1))
   | core.ops.control_flow.ControlFlow.Break residual => do
     let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       AspisR1CurrentPreparedClaim.Concrete.E (core.convert.FromSame AspisR1CurrentPreparedClaim.verifier.Error) residual
     ok (.done r2)) := by
 have he : XRn_Join_usize iter.start.val=iter.start :=
   UScalar.eq_of_val_eq (XRy_ClaimSelect.usize_value iter.start.val (by omega))
 have hread := XSa_ClaimSelect.all_six ops sem s point iter.start.val hp hi
 rw [parser,he] at hread
 rw [AspisR1CurrentPreparedClaim.ClaimScalar.body_eq_source]
 unfold AspisR1CurrentPreparedClaim.ClaimScalar.body
 rw [hn,bind_tc_ok]
 dsimp only
 rw [←hread]
 simp only [bind_map]
 apply congrArg (fun k => XRy_ClaimSelect.read (es sem) s point iter.start.val >>= k)
 funext q
 rw [(coefficient g hg iter.start hi).2.2,bind_tc_ok]
 apply (bind_eq_iff _ _ _).mpr
 rintro ⟨r,dot⟩ hdot
 rfl

#print axioms body
end XSa_DotBody
