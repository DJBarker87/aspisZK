import NMN_241Continuation
set_option autoImplicit false
noncomputable section
namespace NMN_241Suffix
open Aeneas Aeneas.Std Result AdapterRw NLE_Owned
abbrev AuthReply := core.result.Result Unit aspis_r1_cost_probe.verifier.Error
/-- The exact frozen241 continuation after its064 call. Error mapping is an
entered source call and may itself fail/div; emit is entered only on Ok. -/
def afterAuth (ops : Ops) (state : State) (statement : Statement) (reply : AuthReply) : Run PR := do
 let mapped ← errorMap ops state reply
 let flow ← core.result.Result.Insts.CoreOpsTry.branch mapped
 match flow with
 | core.ops.control_flow.ControlFlow.Continue _ => NLE_OwnedStep.emit ops state statement
 | core.ops.control_flow.ControlFlow.Break residual =>
   liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    Unit (core.convert.FromSame PE) residual

def entered (ops : Ops) (state : State) (statement : Statement)
 (publicBytes proof checkpoint : Slice U8) (reply : Result AuthReply) : Run PR :=
 NJU_Log.record (.tx2 state publicBytes proof checkpoint) reply >>= afterAuth ops state statement

theorem success (ops : Ops) (state : State) (statement : Statement) :
 afterAuth ops state statement (.Ok ()) = NLE_OwnedStep.emit ops state statement := rfl
/-- Full ProgramError payload retained; it is never replaced by an ABI code. -/
theorem mapped_error (ops : Ops) (state : State) (statement : Statement)
 (e : aspis_r1_cost_probe.verifier.Error) (pe : PE) (returned : ops.op44 e=.ok pe) :
 afterAuth ops state statement (.Err e) = ⟨.ok (.Err pe),[Event.error state e (.ok pe)]⟩ := by
 simp only [afterAuth, errorMap]
 rw [returned]
 rfl

theorem mapping_failed (ops : Ops) (state : State) (statement : Statement)
 (e : aspis_r1_cost_probe.verifier.Error) (failure : Aeneas.Std.Error)
 (failed : ops.op44 e=.fail failure) :
 afterAuth ops state statement (.Err e) = ⟨.fail failure,[Event.error state e (.fail failure)]⟩ := by
 simp only [afterAuth, errorMap]
 rw [failed]
 rfl

theorem mapping_diverged (ops : Ops) (state : State) (statement : Statement)
 (e : aspis_r1_cost_probe.verifier.Error) (diverged : ops.op44 e=.div) :
 afterAuth ops state statement (.Err e) = ⟨.div,[Event.error state e .div]⟩ := by
 simp only [afterAuth, errorMap]
 rw [diverged]
 rfl

theorem auth_failed (ops : Ops) (state : State) (statement : Statement)
 (publicBytes proof checkpoint : Slice U8) (e : Aeneas.Std.Error) :
 entered ops state statement publicBytes proof checkpoint (.fail e) =
 ⟨.fail e,[Event.tx2 state publicBytes proof checkpoint (.fail e)]⟩ := rfl

theorem auth_diverged (ops : Ops) (state : State) (statement : Statement)
 (publicBytes proof checkpoint : Slice U8) :
 entered ops state statement publicBytes proof checkpoint .div =
 ⟨.div,[Event.tx2 state publicBytes proof checkpoint .div]⟩ := rfl
#print afterAuth
#print success
#print mapped_error
#print mapping_failed
#print mapping_diverged
#print auth_failed
#print auth_diverged
#print axioms success
#print axioms mapped_error
#print axioms mapping_failed
#print axioms mapping_diverged
#print axioms auth_failed
#print axioms auth_diverged
end NMN_241Suffix
