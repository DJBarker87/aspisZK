import NKR_TermAmount
import NKR_TermComposeTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermCompositionFactor
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
open pool_v1.pair_forest_semantic_terminal
/-- Full237 source reference with actual amount precheck and validation. Every
validation Result arm, including ambient fail/div, retains its original place
and no later continuation executes after a rejected/error prefix. -/
def reference (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) := do
 let (_,invalid)←NKR_TermAmount.run pub
 if invalid then ok (.Err .InvalidPublicAmount) else do
  let validation←validate_transition pub
  match validation with
  | .Err e=>ok (.Err e)
  | .Ok _=>NKR_TermComposeTail.run pub claims point lambda chi theta

/-- Unconditional complete source237 factor. No validation-success or returned
child equation is an input. The continuation itself has a separate generic
source theorem deriving all actual child domains and channels internally. -/
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) :
 composition_parts pub claims point lambda chi theta=reference pub claims point lambda chi theta := by
 have amounts:=NKR_TermAmount.source pub
 have literal:=amounts
 unfold NKR_TermAmount.run at literal
 unfold composition_parts reference
 rw [literal,amounts,bind_tc_ok]
 dsimp only [Aeneas.Std.uncurry]
 cases b : NKR_TermAmount.invalid pub.withdrawal_amount with
 | true=>simp only [b,ite_true]
 | false=>
   simp only [b,ite_false]
   have same : {pub with withdrawal_amount:=pub.withdrawal_amount}=pub := by cases pub;rfl
   rw [same]
   cases v : validate_transition pub with
   | fail e=>rfl
   | div=>rfl
   | ok r=>
     cases r with
     | Err e=>rfl
     | Ok u=>cases u;rfl
#print source
#print axioms source
end AspisR1.NKR_TermCompositionFactor
end
