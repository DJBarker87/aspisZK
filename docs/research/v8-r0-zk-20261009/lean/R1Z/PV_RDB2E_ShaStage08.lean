import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 8; constants and bank operands checked by sha-stages.py. -/
def stage08 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank4 b).w3) (⟨0x53380d13,0x4d2c6dfc,0x2e1b2138,0x27b70a85⟩)
  (join pair.1 pair.2,bank4 b)

theorem rounds_at_08 (s : S) (b : Banks) :
    (stage08 s b).1=four s (add ((bank4 b).w3) (⟨0x53380d13,0x4d2c6dfc,0x2e1b2138,0x27b70a85⟩)) :=
  four_source s ((bank4 b).w3) (⟨0x53380d13,0x4d2c6dfc,0x2e1b2138,0x27b70a85⟩)

theorem schedule_at_08 (b : Banks) :
    window0 (stage08 (join b.w0 b.w1) b).2 = advance (window4 b) := phase4 b

#print axioms rounds_at_08
#print axioms schedule_at_08
end R1Z.PV_RDB2E_ShaScalar
