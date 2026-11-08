import PV_LIB_A_F5CallbackStall16
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_F5CallbackTrap16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_A_F5CallbackStall16 (config wait)

def waiting (s : Store Data) (a : Nat) (parents : List Frame) (p : Address) (w : OWNER) (es : List Event) : State :=
  ⟨⟨.running (config s a parents p),w,es⟩,[]⟩
def undefined (s : Store Data) (a : Nat) (parents : List Frame) (p : Address) (w : OWNER) (es : List Event) : State :=
  ⟨⟨.undefined none (config s a parents p).store,w,es⟩,[]⟩

theorem ordinary (s : Store Data) (a : Nat) (parents : List Frame) (p : Address) (w : OWNER) (es : List Event) :
    PV_LIB_SPEC_ControlRuntime.ordinary (waiting s a parents p w es) = some (config s a parents p,wait s p) := by
  have lookup := PV_LIB_SPEC_Tls18Delivery16.lookup
  change PV_LIB_SPEC_Full.programs PV_THR2_RunTlsCallable.descriptors.1 = none at lookup
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,waiting,config,wait,PV_LIB_SPEC_TlsCallable16.config,
    PV_LIB_A_F5ClosurePending16.request,PV_THR2_Catch316Segment.select,lookup]

theorem step (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    (PV_LIB_SPEC_ReachedNative14.step (PV_LIB_SPEC_TlsNative15.cut stack)
      PV_LIB_SPEC_ReachedEnvironment14.parameters ⟨waiting s a parents p w es,issued,consumed⟩).state =
      waiting s a parents p w es ∨
    (PV_LIB_SPEC_ReachedNative14.step (PV_LIB_SPEC_TlsNative15.cut stack)
      PV_LIB_SPEC_ReachedEnvironment14.parameters ⟨waiting s a parents p w es,issued,consumed⟩).state =
      undefined s a parents p w es := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  rw [ordinary]
  dsimp only
  cases origin : PV_LIB_SPEC_ResourceHistory.context ⟨waiting s a parents p w es,issued,consumed⟩
      (config s a parents p) (wait s p) with
  | none => exact Or.inr rfl
  | some ctx =>
    dsimp only [waiting]
    let resources : Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
      PV_LIB_SPEC_ReachedEnvironment14.parameters.environment ctx
    have answer := PV_LIB_A_F5CallbackObstruction16.answer_pending stack resources s a parents p w
    change PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) (config s a parents p) (wait s p).request w =
      some ⟨.pending,w,[]⟩ at answer
    dsimp only [PV_LIB_SPEC_TlsBound15.parameters,resources] at answer
    rw [answer]
    exact Or.inl (PV_LIB_A_F5CallbackStall16.transition stack resources s a parents p w es [])

theorem undefined_step (cut : PV_LIB_SPEC_ReachedNative14.Cut) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ReachedNative14.step cut PV_LIB_SPEC_ReachedEnvironment14.parameters
      ⟨undefined s a parents p w es,issued,consumed⟩ = ⟨undefined s a parents p w es,issued,consumed⟩ := rfl

theorem undefined_run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) (n : Nat) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters n
      ⟨undefined s a parents p w es,issued,consumed⟩ = ⟨undefined s a parents p w es,issued,consumed⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [PV_LIB_SPEC_ReachedNative14.run,undefined_step,ih]

theorem trapped (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) (n : Nat) :
    (PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack)
      PV_LIB_SPEC_ReachedEnvironment14.parameters n ⟨waiting s a parents p w es,issued,consumed⟩).state =
      waiting s a parents p w es ∨
    (PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack)
      PV_LIB_SPEC_ReachedEnvironment14.parameters n ⟨waiting s a parents p w es,issued,consumed⟩).state =
      undefined s a parents p w es := by
  induction n generalizing issued consumed with
  | zero => exact Or.inl rfl
  | succ n ih =>
    let y := PV_LIB_SPEC_ReachedNative14.step (PV_LIB_SPEC_TlsNative15.cut stack)
      PV_LIB_SPEC_ReachedEnvironment14.parameters ⟨waiting s a parents p w es,issued,consumed⟩
    change (PV_LIB_SPEC_ReachedNative14.run _ _ n y).state = waiting s a parents p w es ∨
      (PV_LIB_SPEC_ReachedNative14.run _ _ n y).state = undefined s a parents p w es
    rcases step stack s a parents p w es issued consumed with h | h
    · have hy : y = ⟨waiting s a parents p w es,y.issued,y.consumed⟩ :=
        PV_LIB_A_F170Return16.execution_ext _ _ h rfl rfl
      have eq := congrArg (fun x => (PV_LIB_SPEC_ReachedNative14.run
        (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters n x).state) hy
      exact Or.imp (fun h => eq.trans h) (fun h => eq.trans h) (ih y.issued y.consumed)
    · have hy : y = ⟨undefined s a parents p w es,y.issued,y.consumed⟩ :=
        PV_LIB_A_F170Return16.execution_ext _ _ h rfl rfl
      have eq := congrArg (fun x => (PV_LIB_SPEC_ReachedNative14.run
        (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters n x).state) hy
      exact Or.inr (eq.trans (congrArg Execution.state
        (undefined_run _ s a parents p w es y.issued y.consumed n)))

theorem no_body_entry (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) (n : Nat)
    (body : List PV_STX2_SliceSyntax.Node) :
    ¬ PV_LIB_SPEC_LaneAJoins18.BodyEntry
      (PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack)
        PV_LIB_SPEC_ReachedEnvironment14.parameters n ⟨waiting s a parents p w es,issued,consumed⟩) body := by
  intro ⟨c,status,remaining,not_waiting,done,unwind⟩
  rcases trapped stack s a parents p w es issued consumed n with h | h
  · rw [h] at status
    cases status
    cases not_waiting
  · rw [h] at status
    cases status

#print axioms ordinary
#print axioms step
#print axioms undefined_step
#print axioms undefined_run
#print axioms trapped
#print axioms no_body_entry
end PV_LIB_A_F5CallbackTrap16
