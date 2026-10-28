import NCV_Install
import NCV_ArrayFrame
set_option autoImplicit false
namespace NDB_FirstFailure
/-- Symbolic first failure, without enumerating the finite buffer. -/
theorem first (n : Nat) (good : Nat → Prop) (failure : ¬∀ j, j<n → good j) :
    ∃ bad, bad<n ∧ ¬good bad ∧ ∀ j, j<bad → good j := by
  classical
  have witness : ∃ j, j<n ∧ ¬good j := by
    by_contra h
    apply failure
    intro j hj
    by_contra bad
    exact h ⟨j,hj,bad⟩
  refine ⟨Nat.find witness,(Nat.find_spec witness).1,(Nat.find_spec witness).2,?_⟩
  intro j hj
  by_contra bad
  have minimal:=Nat.find_min' witness (show j<n ∧ ¬good j from ⟨by omega,bad⟩)
  omega
/-- Projection indices used by the repaired master/checkpoint Box harnesses. -/
theorem master_sequences (j : Nat) (bound : j<8) :
    230+j<238 ∧ 230+j-230=j := by omega

theorem checkpoint_sequences (j : Nat) (bound : j<8) :
    74+j<82 ∧ 74+j-74=j := by omega

theorem master_byte_block (block j : Nat) (blocks : block<7) (bound : j<32) :
    6+32*block+j<238 ∧
      6+32*block ≤ 6+32*block+j ∧
      6+32*block+j < 6+32*(block+1) := by omega
#print axioms first
#print axioms master_sequences
#print axioms checkpoint_sequences
#print axioms master_byte_block
end NDB_FirstFailure
set_option autoImplicit false
namespace NDB_ResultCarrier
open Aeneas Aeneas.Std Result

def collapse {A B : Type} (f : B → A) :
    core.result.Result B AdapterRw.solana_program_error.ProgramError → core.result.Result A Unit
  | .Ok b => .Ok (f b)
  | .Err _ => .Err ()

theorem roundtrip {A B : Type} (f : A → B) (g : B → A) (left : ∀ a, g (f a)=a)
    (r : core.result.Result A Unit) : collapse g (NCV_Install.mapReturn f r)=r := by
  cases r with
  | Ok a => simp only [NCV_Install.mapReturn,collapse,left]
  | Err e => cases e;rfl

theorem faithful {A B : Type} (f : A → B) (g : B → A) (left : ∀ a, g (f a)=a)
    (r s : core.result.Result A Unit) : NCV_Install.mapReturn f r=NCV_Install.mapReturn f s ↔ r=s := by
  constructor
  · intro h
    have eq:=congrArg (collapse g) h
    simpa only [roundtrip f g left] using eq
  · intro h;rw [h]

theorem master (r s : core.result.Result NCV_Reference.Master Unit) :
    NCV_Install.mapReturn NCV_Carrier.master r=NCV_Install.mapReturn NCV_Carrier.master s ↔ r=s :=
  faithful _ NCV_Carrier.fromMaster NCV_Carrier.master_roundtrip r s

theorem checkpoint (r s : core.result.Result NCV_Reference.Checkpoint Unit) :
    NCV_Install.mapReturn NCV_Carrier.checkpoint r=NCV_Install.mapReturn NCV_Carrier.checkpoint s ↔ r=s :=
  faithful _ NCV_Carrier.fromCheckpoint NCV_Carrier.checkpoint_roundtrip r s

theorem lane (r s : core.result.Result NCV_Reference.Lane Unit) :
    NCV_Install.mapReturn NCV_Carrier.lane r=NCV_Install.mapReturn NCV_Carrier.lane s ↔ r=s :=
  faithful _ NCV_Carrier.fromLane NCV_Carrier.lane_roundtrip r s
#print axioms roundtrip
#print axioms faithful
#print axioms master
#print axioms checkpoint
#print axioms lane
end NDB_ResultCarrier
