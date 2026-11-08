import PV_LIB_Observation
import PV_STX2_LiveNumbering
import PV_THR2_SourceStoreInterpreter
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Boundary
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

abbrev State (W E : Type) := PV_THR2_IntrinsicState.State W E

/-- The supplied machine executes the concrete five-writer interpreter.
This carrier is data only: its source/leaf adequacy is a separate obligation. -/
structure Machine (W E : Type) where
  carrier : Carrier W Data
  control : Control
  programs : Data → Option PV_STX2_SliceSyntax.Program
  handler : PV_STX2_Native.Request Data → W → Reply W E Data
  values : PV_THR2_SourceStoreLibrary.Values W E

def step {W E : Type} (m : Machine W E) : State W E → State W E :=
  PV_THR2_SourceStoreInterpreter.step m.carrier m.control m.programs m.handler m.values

def run {W E : Type} (m : Machine W E) : Nat → State W E → State W E
  | 0,q => q
  | n+1,q => run m n (step m q)

/-- Excludes completed frames, structured dispatch and intrinsic interception.
For non-child native requests there is no program table lookup. -/
def ConsumedPending {W E : Type} (m : Machine W E) (q : State W E) : Prop :=
  ∃ c wait, q.current.status = .running c ∧ c.frame.completed = none ∧
    c.frame.waiting = some wait ∧ PV_THR2_Catch316Segment.select c = none ∧
    (match wait.request with
      | .child fn _ _ => m.programs fn = none
      | _ => True) ∧
    (m.handler wait.request q.current.world).answer = .pending ∧
    ∃ after, (step m q).current.status = .running after ∧
      after.frame.completed = none ∧ after.frame.waiting = some wait

/-- Own completion before return administration. Intrinsic descendants cannot
complete this row: the suspended suffix must be the entry suffix. -/
def OwnComplete {W E : Type} (entry out : State W E) : Prop :=
  ∃ before after result, entry.current.status = .running before ∧
    out.current.status = .running after ∧
    after.frame.activation = before.frame.activation ∧
    after.callers = before.callers ∧ out.suspended = entry.suspended ∧
    after.frame.completed = some result

/-- A gap is explicit, not silently counted as a successful source result. -/
def RepresentationGap {W E : Type} (q : State W E) : Prop :=
  ∃ address store, q.current.status = .undefined address store

def Terminal {W E : Type} (q : State W E) : Prop :=
  (∃ result store, q.current.status = .returned result store) ∨
  (∃ fault store, q.current.status = .fault fault store) ∨ RepresentationGap q

/-- Pending is recognized on the consumed transition, not by polling a handler
at an arbitrary running configuration. -/
def Boundary {W E : Type} (m : Machine W E) (entry : State W E) (n : Nat) : Prop :=
  OwnComplete entry (run m n entry) ∨ Terminal (run m n entry) ∨
    ∃ k, n = k+1 ∧ ConsumedPending m (run m k entry)

def First {W E : Type} (m : Machine W E) (entry : State W E) (n : Nat) : Prop :=
  Boundary m entry n ∧ ∀ k, k < n → ¬ Boundary m entry k

/-- Every finite prefix remains specified in the infinite case. -/
def Diverges {W E : Type} (m : Machine W E) (entry : State W E) : Prop :=
  ∀ n, ¬ Boundary m entry n

/-- Numbering applies to the active and suspended configurations independently;
no cross-callee equality of the unused activation counter is exported. -/
def Numbered {W E : Type} (q : State W E) : Prop :=
  (∀ c, q.current.status = .running c → PV_STX2_LiveNumbering.Numbered c) ∧
  ∀ c ∈ q.suspended, PV_STX2_LiveNumbering.Numbered c

/-- Public finite outcomes erase process-abort state and all unused counters. -/
def observe {W E : Type} (q : State W E) := PV_LIB.observe q

theorem first_unique {W E : Type} (m : Machine W E) (q : State W E)
    (a b : Nat) (ha : First m q a) (hb : First m q b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact False.elim (hb.2 a h ha.1)
  · exact h
  · exact False.elim (ha.2 b h hb.1)

theorem body_not_pending {W E : Type} (m : Machine W E) (q : State W E)
    (c : Config) (wait : PV_STX2_Native.Waiting Data) (fn : Data) (a : Nat)
    (args : List Data) (body : PV_STX2_SliceSyntax.Program)
    (running : q.current.status = .running c) (waiting : c.frame.waiting = some wait)
    (request : wait.request = .child fn a args) (resolved : m.programs fn = some body) :
    ¬ ConsumedPending m q := by
  rintro ⟨d,w,hd,_,hw,_,dispatch,_⟩
  have dc : d = c := by rw [running] at hd; exact (Status.running.inj hd).symm
  subst d
  have wc : w = wait := by rw [waiting] at hw; exact (Option.some.inj hw).symm
  subst w
  simp only [request,resolved] at dispatch
  cases dispatch

theorem abort_prefix {W E : Type} (s : Store Data) (w : W) (es : List E)
    (stack : List Config) :
    observe (⟨⟨.fault .abort s,w,es⟩,stack⟩ : State W E) =
      PV_LIB.MachineObservation.abort es := rfl

#print axioms first_unique
#print axioms body_not_pending
#print axioms abort_prefix
end PV_LIB_SPEC_Boundary
