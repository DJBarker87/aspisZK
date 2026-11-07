import NNE_InvocationView
set_option autoImplicit false
noncomputable section
namespace NNE_RuntimeTrace
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open Hist_Store CPP_BankState RSL RSL.TAS NNE_Observed

def other (p : S2W_ExtractionBoundary.Program) (before : Bank) (action : Action Bool) :
 Bank × S2X.AccountEvent := CPP_BankState.apply
  (fun _ _ _ => fail .assertionFailure) (fun _ _ _ _ => fail .assertionFailure)
  (fun _ _ _ => .panic) NNE_AbortIndicator.allocator p before action

def noninvoke : Action Bool → Prop
 | .invoke _ => False
 | _ => True

theorem other_eq (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (p : S2W_ExtractionBoundary.Program) (before : Bank) (action : Action Bool)
 (h : noninvoke action) :
 CPP_BankState.apply n1 n2 copy NNE_AbortIndicator.allocator p before action = other p before action := by
 cases action <;> first | contradiction | rfl

/-- Actual entry observations, runtime oracle association, original action and
bank identities. The non-verifier actions retain their existing runtime/Pool
association. Neither constructor contains a verifier-model call or Step. -/
inductive Step (S : Sig) (d : NNE_AcceptanceSig.Data S) (c : S.Ctx)
 (f : TX2_213.Args → SdkState → Env → Observation) :
 Bank → Action Bool → Bank → S2X.AccountEvent → Prop where
 | invoke (before after : Bank) (input : CPP_Invocation.Invocation Bool)
     (env : Env) (event : S2X.AccountEvent) (envrep : S.EnvRep c env)
     (rep : Assoc before after input
       (f (args before input (d.program c)) (state before input) env) event) :
     Step S d c f before (.invoke input) after event
 | other (before after : Bank) (action : Action Bool) (event : S2X.AccountEvent)
     (h : noninvoke action) (rep : other (d.program c) before action = (after,event)) :
     Step S d c f before action after event

inductive Trace (S : Sig) (d : NNE_AcceptanceSig.Data S) (c : S.Ctx)
 (f : TX2_213.Args → SdkState → Env → Observation) :
 Bank → List (Action Bool) → Bank → List S2X.AccountEvent → Prop where
 | nil (bank : Bank) : Trace S d c f bank [] bank []
 | cons {before middle after : Bank} {action : Action Bool} {actions : List (Action Bool)}
     {event : S2X.AccountEvent} {events : List S2X.AccountEvent}
     (head : Step S d c f before action middle event)
     (tail : Trace S d c f middle actions after events) :
     Trace S d c f before (action :: actions) after (event :: events)

theorem step (S : Sig) (d : NNE_AcceptanceSig.Data S) (V : VLib)
 (P : PreparedNew V) (C : TX1_345.S1Lib V) (c : S.Ctx)
 (a1 : NND_A1 (NNE_AcceptanceSig.physical S d) V P C) (hx : S.Exhibited c)
 (f : TX2_213.Args → SdkState → Env → Observation)
 (stage1 : ∀ a s env, TX2_221.stage1Route a.data = true → TX1_344.Ref V P C a s env (f a s env))
 (g2 : ∀ a s env, ASQ8 a.data → Frame s (f a s env))
 (reject : ∀ a s env, TX2_221.admitted a.data = false →
   f a s env = ⟨.ret (.error .invalidInstructionData,s),[]⟩)
 {before after : Bank} {action : Action Bool} {event : S2X.AccountEvent}
 (h : Step S d c f before action after event) :
 CPG_RuntimeTrace.Step (d.native1 (S.model1 c)) (d.native2 (S.model2 c)) d.copy
  NNE_AbortIndicator.allocator (d.program c) before action after event := by
 have he : CPP_BankState.apply (d.native1 (S.model1 c)) (d.native2 (S.model2 c)) d.copy
   NNE_AbortIndicator.allocator (d.program c) before action = (after,event) := by
  cases h with
  | invoke bank input env event envrep rep =>
   exact NNE_InvocationView.invocation S d V P C c a1 hx f stage1 g2 reject
     before after input env envrep event rep
  | other bank action event h rep =>
   rw [other_eq _ _ d.copy (d.program c) before action h]
   exact rep
 have hs := CPG_RuntimeTrace.step_exists (d.native1 (S.model1 c)) (d.native2 (S.model2 c))
   d.copy NNE_AbortIndicator.allocator (d.program c) before action
 rw [he] at hs
 exact hs

theorem executes (S : Sig) (d : NNE_AcceptanceSig.Data S) (V : VLib)
 (P : PreparedNew V) (C : TX1_345.S1Lib V) (c : S.Ctx)
 (a1 : NND_A1 (NNE_AcceptanceSig.physical S d) V P C) (hx : S.Exhibited c)
 (f : TX2_213.Args → SdkState → Env → Observation)
 (stage1 : ∀ a s env, TX2_221.stage1Route a.data = true → TX1_344.Ref V P C a s env (f a s env))
 (g2 : ∀ a s env, ASQ8 a.data → Frame s (f a s env))
 (reject : ∀ a s env, TX2_221.admitted a.data = false →
   f a s env = ⟨.ret (.error .invalidInstructionData,s),[]⟩)
 {before after : Bank} {actions : List (Action Bool)} {events : List S2X.AccountEvent}
 (h : Trace S d c f before actions after events) :
 CPG_RuntimeTrace.Executes (d.native1 (S.model1 c)) (d.native2 (S.model2 c)) d.copy
  NNE_AbortIndicator.allocator (d.program c) before actions after events := by
 induction h with
 | nil bank => exact CPG_RuntimeTrace.Executes.nil bank
 | cons head tail ih =>
  exact CPG_RuntimeTrace.Executes.cons (step S d V P C c a1 hx f stage1 g2 reject head) ih
#print axioms other_eq
#print axioms step
#print axioms executes
end NNE_RuntimeTrace
end
