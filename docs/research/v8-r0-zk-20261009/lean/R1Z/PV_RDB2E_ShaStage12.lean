import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 12; constants and bank operands checked by sha-stages.py. -/
def stage12 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank3 b).w2) (⟨0x34b0bcb5,0x2748774c,0x1e376c08,0x19a4c116⟩)
  (join pair.1 pair.2,bank3 b)

theorem rounds_at_12 (s : S) (b : Banks) :
    (stage12 s b).1=four s (add ((bank3 b).w2) (⟨0x34b0bcb5,0x2748774c,0x1e376c08,0x19a4c116⟩)) :=
  four_source s ((bank3 b).w2) (⟨0x34b0bcb5,0x2748774c,0x1e376c08,0x19a4c116⟩)

theorem schedule_at_12 (b : Banks) :
    window4 (stage12 (join b.w0 b.w1) b).2 = advance (window3 b) := phase3 b

#print axioms rounds_at_12
#print axioms schedule_at_12
end R1Z.PV_RDB2E_ShaScalar
