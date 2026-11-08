import PV_LIB_SPEC_RegistrationGap
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ThreadMachine
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
abbrev Event := PV_RJ4IDB.NativeEvent
abbrev State := PV_THR2_IntrinsicState.State OWNER Event
/-- Data of the combined interpretation proposed by SPEC-C2. No Store delta,
write-definedness, successful reply, sourceStep or desired Post field. -/
structure Machine where
  carrier : Carrier OWNER Data
  control : Control
  programs : Data → Option PV_STX2_SliceSyntax.Program
  handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER Event Data
  resources : Resources
  encode : Encode
  values : PV_THR2_SourceStoreLibrary.Values OWNER Event
/-- Preserve intrinsic priority and the existing OWNER/operator/allocation
layers; change only actual native writer polls. This is a correction CANDIDATE,
not silently substituted for the literal frozen COMMON clause. -/
def step (m : Machine) (q : State) : State :=
  match q.current.status with
  | .running c =>
    match PV_THR2_Catch316Segment.select c with
    | some _ => PV_THR2_OwnInitInterpreterBridged.step m.carrier m.control m.programs
        m.resources m.encode m.handler q
    | none =>
      match PV_THR2_SourceStoreNative.select m.programs c with
      | some _ => PV_THR2_SourceStoreInterpreter.step m.carrier m.control m.programs
          m.handler m.values q
      | none => PV_THR2_OwnInitInterpreterBridged.step m.carrier m.control m.programs
          m.resources m.encode m.handler q
  | _ => PV_THR2_OwnInitInterpreterBridged.step m.carrier m.control m.programs
      m.resources m.encode m.handler q

def run (m : Machine) : Nat → State → State
  | 0,q => q
  | n+1,q => run m n (step m q)
/-- Exact per-configuration interpretation adequacy TARGET, with sourceStep
an external source projection. It is not a MachineSpec or entry hypothesis. -/
def SourceAdequacy (m : Machine) (sourceStep : State → State) : Prop :=
  ∀ q, sourceStep q = step m q
/-- A named target for transport on an actual reachable configuration. -/
def ReachedAgreement (m : Machine) (sourceStep : State → State) (entry : State) : Prop :=
  ∀ n, sourceStep (run m n entry) = step m (run m n entry)
/-- Checked comparison outside listed writer polls, retaining every status. -/
theorem away (m : Machine) (q : State)
    (neutral : ∀ c, q.current.status = .running c →
      PV_THR2_SourceStoreNative.select m.programs c = none) :
    step m q = PV_THR2_OwnInitInterpreterBridged.step m.carrier m.control m.programs
      m.resources m.encode m.handler q := by
  unfold step
  cases status : q.current.status <;> try rfl
  rename_i c
  cases caught : PV_THR2_Catch316Segment.select c
  · simp only [caught,neutral c status]
  · simp only [caught]
/-- At a real ordinary native writer, the exact pinned concrete meaning and
full reply administration are used; no source-store result is assumed. -/
theorem writer (m : Machine) (q : State) (c : Config)
    (site : PV_THR2_SourceStoreNative.Site)
    (running : q.current.status = .running c)
    (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : PV_THR2_SourceStoreNative.select m.programs c = some site) :
    step m q = PV_THR2_SourceStoreInterpreter.step m.carrier m.control m.programs
      m.handler m.values q := by
  simp only [step,running,ordinary,selected]
/-- Regression at the exact source binding which the literal replacement lost. -/
theorem registration (m : Machine) (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (stack : List Config) :
    (step m (PV_LIB_SPEC_RegistrationGap.before s a parents w es stack)).current.world.next =
      w.next+1 := rfl
#print axioms Machine
#print axioms step
#print axioms run
#print axioms SourceAdequacy
#print axioms ReachedAgreement
#print axioms away
#print axioms writer
#print axioms registration
end PV_LIB_SPEC_ThreadMachine
