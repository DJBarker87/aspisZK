import PoolL_Physical
set_option autoImplicit false
namespace AspisR1.PoolL_PhysicalFresh
open Aeneas Aeneas.Std Result PoolL_Physical

theorem excluded (s : Snapshot) (key id expected system : Key) (size : Usize)
    (cp : Occupied s key) (other : PoolL_LengthOccupied.OtherWidth size.val) :
    PoolL_FreshRoleSource.PoolL_fresh_role (observe s key) id expected system
      (decide ((bytes s key).val.length = 0)) (.Ok (bytes s key)) size =
      ok (.Err (.Custom 1095966773#u32)) := by
  have nz : (bytes s key).val.length ≠ 0 := by rcases cp with h | h <;> omega
  simp only [nz,decide_false]
  exact PoolL_FreshRoleReject.occupied _ _ _ _ _ _ cp other
#print axioms excluded
end AspisR1.PoolL_PhysicalFresh
