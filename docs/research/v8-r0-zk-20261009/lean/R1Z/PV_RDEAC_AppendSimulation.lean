import R1Z.PV_RDEA_AppendNoGrowth
import R1Z.PV_CBL_AppendSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDEAC_AppendSimulation
open PV_CBL_StringBytesAdapter PV_RDB1_V183_ReserveWorld

#print alloc.vec.Vec.extend_from_slice
#print alloc.vec.Vec.extend_from_slice_loop
#print core.clone.CloneU8

/-- A representation relation records bytes and capacity separately; the
extracted String alone does not carry the physical allocation header. -/
def Represents (s : String) (b : Buffer U8) : Prop := b.values=encodeList s

theorem empty_represents (b : Buffer U8) (empty : b.values=[]) : Represents "" b := by
  exact empty

#print axioms empty_represents
end R1Z.PV_RDEAC_AppendSimulation
