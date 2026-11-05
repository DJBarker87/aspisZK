import NHF_Prefix
import NHF_HeapPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_Packets
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

def filled (reserved : Bool) {T : Type} (_copy : core.marker.Copy T) (n : Usize) (value : T) :
 Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error) := do
 let r ← OraclePortStdAllocation.filled n value reserved
 ok (match r with | .ok v => .Ok v | .error _ => .Err .Allocation)

def values (input output : Slice U8) :
 Result (core.result.Result Unit compact.CodecError × Slice U8) := do
 let (r,after) ← NFU_Retarget.compact.expand_values input output
 ok ((match r with | .Ok u => .Ok u | .Err e => .Err (match e with
   | .Length => .Length | .NonZeroHigh => .NonZeroHigh | .NonCanonical => .NonCanonical)),after)

def installed (base : Ops) (reserved : Bool) : Ops :=
 {ConcreteConstants.withConstants base with
   op1:=filled reserved,
   op5:=InstalledPreparation.sourceView,
   op10:=AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues,
   op11:=values}

#print installed
end AspisR1.NHL_Packets
