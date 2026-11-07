import NMP_ObservedSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedBeginError
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_ObservedSteps
open NMT_CallTree (run Event)
/-- The complete begin Err reply includes its post-transcript in the call log;
no mark1 or finish136 call is appended. -/
theorem stopped_prefix {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix)
 (t after : r1_wire.SemanticTranscript H) (e : r1_wire.Error)
 (h : c.c5 s.digest p t = .ok (.Err e,after)) :
 run (execute c 3 (.begin_ s p t)) =
 (.ok (.Err e),[Event.call "TX1:150/begin" (p,t)
  (.ok ((.Err e : core.result.Result aspis_core.state_only_prefix.r0.Challenges r1_wire.Error),after))]) := by
 rw [execute]
 simp only [step]
 rw [h]
 rfl
#print axioms stopped_prefix
end AspisR1.NMP_ObservedBeginError
