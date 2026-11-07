import NMX_R2_InverseSlice
import NMX_MasterValue
import NMX_CheckpointValue
import NMX_R2_Carrier
set_option autoImplicit false
noncomputable section
namespace LIB_AccountDecoderReuse
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier

def master (input : RSL.Bytes) : Option RSL.Master :=
 match NMX_R2_InverseSlice.fromBytes input with
 | none => none
 | some raw => match NMX_MasterValue.decoded raw with
   | .Err _ => none
   | .Ok value => some (NMX_R2_Carrier.master value)

def checkpoint (input : RSL.Bytes) : Option RSL.Checkpoint :=
 match NMX_R2_InverseSlice.fromBytes input with
 | none => none
 | some raw => match NMX_CheckpointValue.decoded raw with
   | .Err _ => none
   | .Ok value => some (NMX_R2_Carrier.checkpoint value)

/-- Only the two relevant decoder fields are selected here. Every other
library component remains the caller's fixed CLOSED model or OPEN234 model. -/
def install (base : RSL.PoolLib) : RSL.PoolLib :=
 {base with decodeMaster := master,decodeCheckpoint := checkpoint}

theorem master_same (b : Slice U8) :
 master (bytes b) = match NMX_MasterValue.decoded b with
 | .Err _ => none
 | .Ok value => some (NMX_R2_Carrier.master value) := by
 unfold master
 rw [NMX_R2_InverseSlice.roundtrip]

theorem checkpoint_same (b : Slice U8) :
 checkpoint (bytes b) = match NMX_CheckpointValue.decoded b with
 | .Err _ => none
 | .Ok value => some (NMX_R2_Carrier.checkpoint value) := by
 unfold checkpoint
 rw [NMX_R2_InverseSlice.roundtrip]
#print axioms master_same
#print axioms checkpoint_same
end LIB_AccountDecoderReuse
end
