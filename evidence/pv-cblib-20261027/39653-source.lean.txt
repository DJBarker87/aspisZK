import R1Z.PV_CBL_Op208Outcomes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_Op208FailureFacts
open ProverRwFull
set_option autoImplicit false

theorem failure_iff (base : ExternalTypes)
    (compress : PV_CBL_Op208Extracted.Compression base)
    (self : PV_CBL_ShaCore.Core) (blocks : PV_CBL_ShaTypes.Blocks base) (e : Error) :
    PV_CBL_Op208Extracted.update_blocks base compress self blocks = fail e ↔
      compress self.state blocks = fail e := by
  rw [PV_CBL_Op208Outcomes.full_result]
  cases hc : compress self.state blocks <;> simp [hc]

theorem divergence_iff (base : ExternalTypes)
    (compress : PV_CBL_Op208Extracted.Compression base)
    (self : PV_CBL_ShaCore.Core) (blocks : PV_CBL_ShaTypes.Blocks base) :
    PV_CBL_Op208Extracted.update_blocks base compress self blocks = div ↔
      compress self.state blocks = div := by
  rw [PV_CBL_Op208Outcomes.full_result]
  cases hc : compress self.state blocks <;> simp [hc]

#print axioms failure_iff
#print axioms divergence_iff
end R1Z.PV_CBL_Op208FailureFacts
