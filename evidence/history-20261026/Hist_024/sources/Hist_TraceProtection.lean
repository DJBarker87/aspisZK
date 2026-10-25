import Hist_StepProtection
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_TraceProtection
open Aeneas Aeneas.Std Result Hist_Store

/-- Arbitrarily many accepted writer/reader and foreign-runtime actions are
allowed. Their own source/ownership checks derive every history protection
field; the trace need not be empty or assumed to avoid the protected key. -/
theorem trace_frame (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (before after : Store) (key : Nat) (events : List S2X.AccountEvent)
    (trace : Trace ops program before events after) :
    (before key).owner = program → Initialized (before key).data →
      (∀ event ∈ events, S2X.Preserves key event) ∧ after key = before key := by
  induction trace with
  | nil => intro owner initialized; exact ⟨by simp,rfl⟩
  | @cons before middle after event events step trace ih =>
    intro owner initialized
    obtain ⟨head,frame⟩ := Hist_StepProtection.step_frame ops program before middle key event step owner initialized
    obtain ⟨tail,final⟩ := ih (by rw [frame]; exact owner) (by rw [frame]; exact initialized)
    constructor
    · intro e member
      rcases List.mem_cons.mp member with same | rest
      · subst e; exact head
      · exact tail e rest
    · exact final.trans frame

#print axioms trace_frame
end AspisR1.Hist_TraceProtection
end
