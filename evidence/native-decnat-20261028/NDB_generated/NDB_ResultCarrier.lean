import NCV_Install
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
