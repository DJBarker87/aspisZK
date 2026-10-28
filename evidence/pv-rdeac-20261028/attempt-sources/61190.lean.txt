import R1Z.PV_RDEAC_EndpointInstance
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_ABI

/-- Explicit deployed architecture specialization. This hypothesis is the
existing source/native carrier ABI boundary, not a witness restriction and not
an additional field of the capped privacy trust list. -/
theorem word_room (target : System.Platform.numBits=64) : 9223372036854775808≤Usize.max := by
  rw [Usize.max,Usize.numBits,target]
  norm_num

#print axioms word_room
end R1Z.PV_RDEAC_ABI
