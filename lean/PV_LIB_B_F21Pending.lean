import PV_STX2_Source7IterationBindings
set_option autoImplicit false
noncomputable section
namespace PV_LIB_B_F21Pending
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
abbrev Handler := PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data
/-- BEFORE: a fallback pending reply can be ignored by a BODY push or by
completion administration. Kept for the explicit correction comparison. -/
def LegacyPoll (resources : Resources) (encode : Encode)
    (H : Handler) (c : Config) (w : OWNER) : Prop :=
  ∃ wait, c.frame.waiting = some wait ∧
    (PV_STX2_Source7IterationHandler.handler resources encode c H wait.request w).answer = .pending
/-- AFTER: only a reply actually consumed at a native poll. This is the
existing f21 correction, stated over its literal iteration handler. -/
def NativePoll (resources : Resources) (encode : Encode)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : Handler) (c : Config) (w : OWNER) : Prop :=
  c.frame.completed = none ∧ ∃ wait, c.frame.waiting = some wait ∧
    (match wait.request with | .child fn _ _ => P fn = none | _ => True) ∧
    (PV_STX2_Source7IterationHandler.handler resources encode c H wait.request w).answer = .pending
/-- Corrected full prefix recognizer. The actual source iteration step,
world, event prefix and result are fixed before testing the consumed reply. -/
def Pending (resources : Resources) (encode : Encode)
    (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler)
    (entry : Prefix OWNER PV_RJ4IDB.NativeEvent) (fuel : Nat)
    (out : Prefix OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  ∃ k c w es, fuel = k+1 ∧
    PV_STX2_Source7IterationBindings.advance resources encode C K P H k entry = ⟨.running c,w,es⟩ ∧
    NativePoll resources encode P H c w ∧
    out = PV_STX2_Source7IterationBindings.advance resources encode C K P H (k+1) entry

theorem forget (resources : Resources) (encode : Encode)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (c : Config) (w : OWNER)
    (poll : NativePoll resources encode P H c w) : LegacyPoll resources encode H c w := by
  rcases poll with ⟨_,wait,waiting,_,answer⟩
  exact ⟨wait,waiting,answer⟩
/-- This excludes the actual f21/s581 BODY-push shape independently of the
ignored fallback answer; the old false-pending diagnostic is retained. -/
theorem rejects_body (resources : Resources) (encode : Encode)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (c : Config) (w : OWNER)
    (wait : PV_STX2_Native.Waiting Data) (fn : Data) (a : Nat) (args : List Data)
    (body : PV_STX2_SliceSyntax.Program) (waiting : c.frame.waiting = some wait)
    (request : wait.request = .child fn a args) (resolved : P fn = some body) :
    ¬ NativePoll resources encode P H c w := by
  rintro ⟨_,other,issued,nativeOnly,_⟩
  have same : other = wait := Option.some.inj (issued.symm.trans waiting)
  subst other
  rw [request] at nativeOnly
  change P fn = none at nativeOnly
  rw [resolved] at nativeOnly
  cases nativeOnly

theorem rejects_completed (resources : Resources) (encode : Encode)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (c : Config) (w : OWNER)
    (result : Aeneas.Std.Result Data) (done : c.frame.completed = some result) :
    ¬ NativePoll resources encode P H c w := by
  intro poll
  have none := poll.1
  rw [done] at none
  cases none
#print axioms LegacyPoll
#print axioms NativePoll
#print axioms Pending
#print axioms forget
#print axioms rejects_body
#print axioms rejects_completed
end PV_LIB_B_F21Pending
