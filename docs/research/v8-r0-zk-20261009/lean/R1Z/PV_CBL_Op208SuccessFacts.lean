import R1Z.PV_CBL_Op208Outcomes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_Op208SuccessFacts
open ProverRwFull
set_option autoImplicit false

theorem success_iff (base : ExternalTypes)
    (compress : PV_CBL_Op208Extracted.Compression base)
    (self next : PV_CBL_ShaCore.Core) (blocks : PV_CBL_ShaTypes.Blocks base) :
    PV_CBL_Op208Extracted.update_blocks base compress self blocks = ok next ↔
      compress self.state blocks = ok next.state ∧
      next.block_len = PV_CBL_Op208Outcomes.nextCount base self blocks := by
  rw [PV_CBL_Op208Outcomes.full_result]
  cases hc : compress self.state blocks <;> cases next <;> simp [hc,eq_comm]
#print axioms success_iff
end R1Z.PV_CBL_Op208SuccessFacts
