import PV_FN_THREAD_f6ScopeContinuation
import PV_THR2_ScopeCatchCall
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6CatchRequest
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Two return slots on the actual124 final store; no old store substitution. -/
def returned (t : Store Data) (child a : Nat) (arc : Data) : Store Data :=
  write (write t ⟨child,0,[]⟩ (some arc)) ⟨a,3,[]⟩ (some arc)

def prepared (t : Store Data) (child a : Nat) (arc capture : Data) : Store Data :=
  PV_THR2_ScopeCaptureWrap.prepared
    (PV_THR2_ScopeCapturePrefix.prepared
      (PV_THR2_ScopeValue.prepared (returned t child a arc) a arc) a) a capture

def pending (t : Store Data) (child a : Nat) (parents : List Frame) (arc capture : Data) : Config :=
  PV_THR2_ScopeCatchCall.pending (prepared t child a arc capture) a parents
    (PV_THR2_ScopeCaptureWrap.value a capture)

/-- Entry capture survives the source constructor/argument prefix by shape. -/
theorem entry_capture (s : Store Data) (a : Nat) (parents : List Frame)
    (x y z : Data) (live : a < s.nextActivation) :
    (PV_FN_THREAD_f6ScopeData.pending s a parents x y z).store.cells ⟨a,1,[]⟩ = s.cells ⟨a,1,[]⟩ := by
  have fresh (k j : Nat) : (⟨a,1,[]⟩ : Address) ≠ ⟨s.nextActivation+k,j,[]⟩ := by
    intro eq
    exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le live (Nat.le_add_right _ _))) (congrArg Address.activation eq)
  have fresh0 (j : Nat) : (⟨a,1,[]⟩ : Address) ≠ ⟨s.nextActivation,j,[]⟩ := fresh 0 j
  simp [PV_FN_THREAD_f6ScopeData.pending,PV_THR2_ScopeArcCall.pending,
    PV_THR2_ScopeArcCall.before,PV_THR2_ScopeData.prepared,
    PV_FN_THREAD_f6ConstructorRun.first,PV_FN_THREAD_f6ConstructorRun.second,
    PV_FN_THREAD_f6ConstructorRun.third,PV_THR2_ScopePrologue.prepared,
    PV_THR2_StaticCall.pending,PV_THR2_StaticReply.returnedStore,
    PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,fresh,fresh0,Nat.add_assoc]

/-- The124 contract's caller-cell frame consumes the exact issued entry. This
is an OPEN dependency projection, to be supplied by W2's full contract. It is
not an additional endpoint premise, a native reply restriction or a CLOSED row. -/
theorem capture_from124 (s t : Store Data) (a : Nat) (parents : List Frame)
    (x y z capture : Data) (live : a < s.nextActivation)
    (entry : s.cells ⟨a,1,[]⟩ = some capture)
    (thread_f124_frame : ∀ p : Address, p.activation < s.nextActivation+3 →
      t.cells p = (PV_FN_THREAD_f6ScopeData.pending s a parents x y z).store.cells p) :
    t.cells ⟨a,1,[]⟩ = some capture := by
  rw [thread_f124_frame _ (show a < s.nextActivation+3 by omega),entry_capture s a parents x y z live,entry]

/-- Derive capture readbacks on the final store, then execute source1917-1989
up to the actual125 request. `capture_cell` is internal; capture_from124 derives
it from entry Pre and the named callee frame, never from a future-read premise. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (child a : Nat) (parents : List Frame) (b : Bool)
    (arc capture : Data) (w : W) (es : List E) (stack : List Config)
    (capture_cell : t.cells ⟨a,1,[]⟩ = some capture) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl P H 20
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 26},parents,
        returned t child a arc⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (pending t child a parents arc capture),w,es⟩,stack⟩ := by
  rw [show 20 = 9 + (6 + (4 + 1)) from rfl,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6ScopeContinuation.scope base ctl P H _ a parents b arc w es stack (by simp [returned,write]),
    PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6ScopeContinuation.reference base ctl P H _ a parents b w es stack,
    PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6ScopeContinuation.wrap base ctl P H _ a parents b capture w es stack
      (by simp [PV_THR2_ScopeCapturePrefix.prepared,PV_THR2_ScopeValue.prepared,returned,write,capture_cell])
      (by simp [PV_THR2_ScopeCapturePrefix.prepared,write])]
  simp only [PV_THR2_IntrinsicState.advance]
  rw [PV_THR2_IntrinsicCompatible.step _ _ P H _ w es stack
    (PV_THR2_IntrinsicCompatible.not_waiting _ rfl),
    PV_THR2_ScopeCatchCall.issue _ ctl P H _ a parents
      (PV_THR2_ScopeCaptureWrap.value a capture) w (by simp [PV_THR2_ScopeCaptureWrap.prepared,write])]
  simp only [List.append_nil]
  rfl

#print axioms entry_capture
#print axioms capture_from124
#print axioms run
end PV_FN_THREAD_f6CatchRequest
