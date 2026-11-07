import PV_FN_THREAD_f6ScopeContinuation
import PV_THR2_ScopeCatchCall
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6OwnContinuation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Only f6's own source writes after1916, on an arbitrary callee Post store.
No f124 cells, return administration, final stores or internal prefixes occur. -/
def prepared (t : Store Data) (a : Nat) (arc capture : Data) : Store Data :=
  PV_THR2_ScopeCaptureWrap.prepared
    (PV_THR2_ScopeCapturePrefix.prepared (PV_THR2_ScopeValue.prepared t a arc) a) a capture

def pending (t : Store Data) (a : Nat) (parents : List Frame) (arc capture : Data) : Config :=
  PV_THR2_ScopeCatchCall.pending (prepared t a arc capture) a parents
    (PV_THR2_ScopeCaptureWrap.value a capture)

/-- Straight segment1917-1989, exactly20 own transitions. The two cell clauses
are INTERNAL post projections; this helper is not a call-entry contract. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (arc capture : Data) (w : W) (es : List E) (stack : List Config)
    (arc_cell : t.cells ⟨a,3,[]⟩ = some arc)
    (capture_cell : t.cells ⟨a,1,[]⟩ = some capture) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl P H 20
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 26},parents,
        t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (pending t a parents arc capture),w,es⟩,stack⟩ := by
  rw [show 20 = 9 + (6 + (4 + 1)) from rfl,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6ScopeContinuation.scope base ctl P H _ a parents b arc w es stack arc_cell,
    PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6ScopeContinuation.reference base ctl P H _ a parents b w es stack,
    PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6ScopeContinuation.wrap base ctl P H _ a parents b capture w es stack
      (by simp [PV_THR2_ScopeCapturePrefix.prepared,PV_THR2_ScopeValue.prepared,write,capture_cell])
      (by simp [PV_THR2_ScopeCapturePrefix.prepared,write])]
  simp only [PV_THR2_IntrinsicState.advance]
  rw [PV_THR2_IntrinsicCompatible.step _ _ P H _ w es stack
    (PV_THR2_IntrinsicCompatible.not_waiting _ rfl),
    PV_THR2_ScopeCatchCall.issue _ ctl P H _ a parents
      (PV_THR2_ScopeCaptureWrap.value a capture) w (by simp [PV_THR2_ScopeCaptureWrap.prepared,write])]
  simp only [List.append_nil]
  rfl

/-- Own source stores preserve every other activation. -/
theorem frame (t : Store Data) (a : Nat) (arc capture : Data) (p : Address)
    (outside : p.activation ≠ a) :
    (prepared t a arc capture).cells p = t.cells p := by
  have neq (i : Nat) : p ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  simp [prepared,PV_THR2_ScopeValue.prepared,PV_THR2_ScopeCapturePrefix.prepared,
    PV_THR2_ScopeCaptureWrap.prepared,write,neq]

/-- Issuing125 tracks only its fresh argument cell, separately from f6 locals. -/
theorem issued_frame (t : Store Data) (a : Nat) (parents : List Frame)
    (arc capture : Data) (p : Address) (old : p.activation < t.nextActivation)
    (outside : p.activation ≠ a) :
    (pending t a parents arc capture).store.cells p = t.cells p := by
  have own (i : Nat) : p ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  have fresh : p ≠ (⟨t.nextActivation,1,[]⟩ : Address) := by
    intro eq
    exact (Nat.ne_of_lt old) (congrArg Address.activation eq)
  change (write (write (prepared t a arc capture) ⟨a,11,[]⟩ none)
    ⟨t.nextActivation,1,[]⟩ (some (PV_THR2_ScopeCaptureWrap.value a capture))).cells p = t.cells p
  simp only [write,own,fresh,ite_false]
  exact frame t a arc capture p outside

#print axioms run
#print axioms frame
#print axioms issued_frame
end PV_FN_THREAD_f6OwnContinuation
