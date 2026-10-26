import PoolL_Physical
set_option autoImplicit false
namespace AspisR1.PoolL_PhysicalAllocate
open Aeneas Aeneas.Std Result PoolL_Physical

theorem excluded (s : Snapshot) (key system loader : Key) (payer sys : Account)
    (cp : Occupied s key) :
    PoolL_AllocateSource.allocatePrefix (readEmpty s) system loader payer (observe s key) sys ≠
      ok (.Ok ()) := PoolL_AllocateReject.nonempty _ _ _ _ _ _ (not_empty s key cp)
#print axioms excluded
end AspisR1.PoolL_PhysicalAllocate
