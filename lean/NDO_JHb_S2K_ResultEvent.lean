import NDO_JHb_S2K_ResultEncoding
import NDO_JHb_S2K_StatementLane
import S2I_ReturnData

/-! Source field-boundary byte/effect composition. This is the returning
syscall suffix, not an installed whole-native-emitter child. Validation and
native caller reachability must still precede this cut. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.ResultEvent
open S2I.ReturnData

def emitFields {A E : Type} (syscall : State A E → List U8 → Result (State A E))
    (state : State A E) (master selected nullifier : Array U8 32#usize)
    (kind lane : U8) (afterstate : Array U8 688#usize) := do
  let out ← S2K_ResultBytes.S2K_reference_bytes master selected nullifier kind lane afterstate
  syscall state out.val

theorem source_event {A E : Type}
    (syscall : State A E → List U8 → Result (State A E))
    (runtime : RuntimePremise syscall) (state : State A E)
    (master selected nullifier : Array U8 32#usize)
    (kind lane : U8) (afterstate : Array U8 688#usize) :
    let out := ResultEncoding.stores (Array.repeat 792#usize 0#u8)
      master selected nullifier kind lane afterstate
    emitFields syscall state master selected nullifier kind lane afterstate = ok (set state out.val) ∧
    out.val.length = 792 ∧ out.val ≠ [] ∧
    (set state out.val).accounts = state.accounts ∧
    (set state out.val).events = state.events ++ [.setReturnData out.val] := by
  dsimp only
  let out := ResultEncoding.stores (Array.repeat 792#usize 0#u8)
    master selected nullifier kind lane afterstate
  have width : out.val.length = 792 := out.property
  have event := nonempty_event syscall runtime state out.val width
  refine ⟨?_,width,event.2.1,event.2.2.1,event.2.2.2⟩
  unfold emitFields
  rw [ResultEncoding.source_value]
  exact event.1

#print axioms source_event
end AspisR1.S2K.ResultEvent
