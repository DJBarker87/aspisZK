import NLM_CodeStep
import NLM_PacketTypes
import NIV_RawBoundary
set_option autoImplicit false
noncomputable section
namespace NLM_Process221
open Aeneas Aeneas.Std AspisR1 NLM_PacketTypes AspisR1.CheckpointBytes5Effect
abbrev PR := core.result.Result Unit Hiq_DispatchSource.PE
inductive Child where | init | write | finalize | first | second
structure Frame (Account : Type) where
 program : Hiq_DispatchSource.Key
 accounts : Slice Account
 data : Slice U8
structure State (Account Ambient : Type) where
 frame : Frame Account
 world : World Ambient
 head : Option (Option U8) := none
abbrev Out (Ambient : Type) := PR × World Ambient
abbrev ChildCode (Account Ambient : Type) :=
 Child → Frame Account → World Ambient → Code (Out Ambient)
abbrev ChildObservation (Account Ambient : Type) :=
 Child → Frame Account → World Ambient → NGP_L181.Observation (Out Ambient)
/-- Full child hash schedule and returned caller frame at the SAME original
arguments. An intermediate MODEL interface, not an admitted native row packet. -/
def Packet {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (observed : ChildObservation Account Ambient) : Prop :=
 ∀ kind frame world,NHZ_DRIVER.Cuts hashv (callee kind frame world)
  (observed kind frame world).result (observed kind frame world).attempted
end NLM_Process221
