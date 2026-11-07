import NNE_RecordSig
set_option autoImplicit false
noncomputable section
namespace NNE_TraceInstantiation
open Aeneas Aeneas.Std AspisR1 CPP_BankState RSL RSL.TAS NNE_Observed

def stamp (input : CPP_Invocation.Invocation Bool) (o : Observation) : CPP_Invocation.Invocation Bool :=
 {input with call := {input.call with state := completed o}}

/-- The abort indicator is computed from the actual observation; stamping
cannot change that observation's original args or SDK pre-state. -/
theorem stamp_args (before : Bank) (input : CPP_Invocation.Invocation Bool) (o : Observation)
 (p : S2W_ExtractionBoundary.Program) : args before (stamp input o) p = args before input p := rfl

theorem stamp_state (before : Bank) (input : CPP_Invocation.Invocation Bool) (o : Observation) :
 state before (stamp input o) = state before input := rfl

theorem stamp_bit (input : CPP_Invocation.Invocation Bool) (o : Observation) :
 (stamp input o).call.state = completed o := rfl

theorem error (before : Bank) (input : CPP_Invocation.Invocation Bool)
 (pe : ProgramError) (post : SdkState) (es : List Event) :
 Assoc before before (stamp input ⟨.ret (.error pe,post),es⟩)
   ⟨.ret (.error pe,post),es⟩ .rollback := ⟨rfl,rfl,rfl⟩

theorem abort (before : Bank) (input : CPP_Invocation.Invocation Bool) (es : List Event) :
 Assoc before before (stamp input ⟨.abort,es⟩) ⟨.abort,es⟩ .rollback := ⟨rfl,rfl,rfl⟩

theorem saved (post : SdkState) (i : Nat) (v : alloc.vec.Vec U8) :
 NNE_PhysicalAccepted.Out1 v ⟨.ret (.ok (),post),[.write i (S2W_ReturnedCheckpoint.nativeBytes v)]⟩ := by
 intro j bs h
 simp only [List.mem_singleton,Event.write.injEq] at h
 exact h.2

theorem empty_trace (S : Sig) (d : NNE_AcceptanceSig.Data S) (c : S.Ctx)
 (f : TX2_213.Args → SdkState → Env → Observation) (before : Bank) :
 NNE_RuntimeTrace.Trace S d c f before [] before [] := NNE_RuntimeTrace.Trace.nil before

/-- Every verifier step of either physical trace has the exit-derived state.
Neither this theorem nor the trace representation assumes an allocator law. -/
theorem invocation_bit (S : Sig) (d : NNE_AcceptanceSig.Data S) (c : S.Ctx)
 (f : TX2_213.Args → SdkState → Env → Observation)
 {before after : Bank} {input : CPP_Invocation.Invocation Bool} {event : S2X.AccountEvent}
 (h : NNE_RuntimeTrace.Step S d c f before (.invoke input) after event) :
 ∃ env, S.EnvRep c env ∧
 (input.call.state = true ↔ ∃ r post,
   (f (args before input (d.program c)) (state before input) env).exit = .ret (r,post)) := by
 cases h with
 | invoke bank input env event envrep rep =>
  exact ⟨env,envrep,NNE_Observed.state_iff _ _ _ _ _ rep⟩
 | other bank action event hn rep => contradiction
#print axioms stamp_args
#print axioms stamp_state
#print axioms stamp_bit
#print axioms error
#print axioms abort
#print axioms saved
#print axioms empty_trace
#print axioms invocation_bit
end NNE_TraceInstantiation
end
