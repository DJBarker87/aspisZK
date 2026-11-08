import NNH_HostOracle
import NLL_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_NativeOracleSlots
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
variable (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
abbrev env := DGP_HostDigest.envInst H pda clock r
abbrev part := LIBB_PartitionEnv.H (env H pda clock r)

theorem node (request : NJP_RowModel.Request) :
 NJP_RequestTransport.hash (MultiproofConePhysicalTransport.rawOracle (part H pda clock r)) request =
 NJP_RequestTransport.hash (MultiproofConePhysicalTransport.rawOracle H) request := by
 unfold NJP_RequestTransport.hash NJP_RequestTransport.address MultiproofConePhysicalTransport.rawOracle
 rw [NNH_HostOracle.node_oracle]

theorem view (H1 H2 : Bytes → State) (proof : Slice U8) (lo : Usize) (key : U64) :
 NLL.view H1 proof lo key = NLL.view H2 proof lo key := by
 unfold NLL.view
 rfl

theorem nodeView (H1 H2 : Bytes → State) (proof : Slice U8) (slot : Usize) :
 NLL.nodeView H1 proof slot = NLL.nodeView H2 proof slot := by
 unfold NLL.nodeView
 rfl

theorem entryKeys (H1 H2 : Bytes → State) (raw : Array U32 22#usize) (batch : Nat) (kind : Usize) :
 NLL.entryKeys H1 raw batch kind = NLL.entryKeys H2 raw batch kind := by
 unfold NLL.entryKeys
 rfl

theorem digest (proof : Slice U8) (kind lo : Usize) (f : NLL.Frame) :
 NLL.digest (part H pda clock r) proof kind lo f = NLL.digest H proof kind lo f := by
 unfold NLL.digest
 rw [view (part H pda clock r) H,NNH_HostOracle.leaf_oracle]

theorem event (proof : Slice U8) (kind lo : Usize) (f : NLL.Frame) :
 NLL.event (part H pda clock r) proof kind lo f = NLL.event H proof kind lo f := by
 unfold NLL.event
 rw [view (part H pda clock r) H,digest H pda clock r]
#print axioms node
#print axioms view
#print axioms nodeView
#print axioms entryKeys
#print axioms digest
#print axioms event
end AspisR1.NNH_NativeOracleSlots
end
