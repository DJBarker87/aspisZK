import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S043
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 43: raw; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (laneMasterBytes : Array U8 32#usize)
 (master : Box Master)
 (lane : Box Lane)
 (next : Bool → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  lane.payload.master laneMasterBytes)) next) ()) =
 ((core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  lane.payload.master laneMasterBytes)) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ()) := by
 exact NMX_ResultSteps.raw ops owners _ next
#print axioms step
end NMX_S043
end
