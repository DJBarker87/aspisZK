import NLH_TermAmount
import NLH_TermComposeTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_TermCompositionFactor
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
open pool_v1.pair_forest_semantic_terminal
/-- Full237 source reference with actual amount precheck and validation. Every
validation Result arm, including ambient fail/div, retains its original place
and no later continuation executes after a rejected/error prefix. -/
def reference (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) : Result (core.result.Result NKR_TermTail.Carrier NKR_TermTail.Error) := do
 let (_,invalid)←NLH_TermAmount.run pub
 if invalid then ok (.Err .InvalidPublicAmount) else do
  let validation←validate_transition pub
  match validation with
  | .Err e=>ok (.Err e)
  | .Ok _=>NLH_TermComposeTail.run pub claims point lambda chi theta

/-- Unconditional complete source237 factor. No validation-success or returned
child equation is an input. The continuation itself has a separate generic
source theorem deriving all actual child domains and channels internally. -/
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) :
 composition_parts pub claims point lambda chi theta=reference pub claims point lambda chi theta := by
 have contEq :
  (do let r←validate_transition pub
      let cf←core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _=>NLH_TermComposeTail.run pub claims point lambda chi theta
      | core.ops.control_flow.ControlFlow.Break residual=>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          NKR_TermTail.Carrier (core.convert.FromSame PoolV1PairForestSemanticTerminalErrorV1) residual)=
  (do let r←validate_transition pub
      match r with
      | .Err e=>ok (.Err e)
      | .Ok _=>NLH_TermComposeTail.run pub claims point lambda chi theta) := by
   cases v : validate_transition pub with
   | fail e=>rfl
   | div=>rfl
   | ok r=>cases r <;> rfl
 unfold composition_parts reference NLH_TermAmount.run
 cases h : pub.withdrawal_amount with
 | none=>
   simp only [h,bind_tc_ok,Aeneas.Std.uncurry,Bool.false_eq_true,ite_false]
   have same : {pub with withdrawal_amount:=none}=pub := by rw [←h]
   rw [same]
   exact contEq
 | some a=>
   by_cases zero : a=0#u32
   · simp only [h,if_pos zero,bind_tc_ok,Aeneas.Std.uncurry,ite_true]
   · have shift : (1#u32 <<< 30#u32 : Result U32)=ok 1073741824#u32 := by rfl
     simp only [h,if_neg zero,shift,bind_tc_ok,Aeneas.Std.uncurry]
     by_cases large : a>=1073741824#u32
     · simp only [large,decide_true,ite_true]
     · simp only [large,decide_false,Bool.false_eq_true,ite_false]
       have same : {pub with withdrawal_amount:=some a}=pub := by rw [←h]
       rw [same]
       exact contEq

#print source
#print axioms source
end AspisR1.NLH_TermCompositionFactor
end
