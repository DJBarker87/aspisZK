import NMX_R3_FrontierBridge
import NMX_R3_Slices
import NMX_R3_Word64
import NMX_R3_Zero
import NMX_R3_Equality
import NMX_R3_ByteCompare
set_option autoImplicit false
namespace NMX_R3_LaneCarrier
open Aeneas Aeneas.Std RSL NMX_R3_ByteCarrier

def key (a : Array U8 32#usize) : B32 :=
 ⟨a.val.map byte, by rw [List.length_map, a.property]; scalar_tac⟩
def lane (a : NCV_Reference.Lane) : LaneState :=
 ⟨byte a.bump, key a.master, byte a.lane_id,
  ⟨long a.next_leaf_index, a.root.val.map word,
   a.frontier.val.map (fun row => row.val.map word)⟩⟩
def result (r : core.result.Result NCV_Reference.Lane Unit) : Option LaneState :=
 match r with
 | .Ok a => some (lane a)
 | .Err () => none

/-- Every owned key byte and its exact width is retained in the canonical key. -/
theorem key_bytes (a : Array U8 32#usize) : (key a).bytes = a.val.map byte := rfl
#print axioms key_bytes
end NMX_R3_LaneCarrier
