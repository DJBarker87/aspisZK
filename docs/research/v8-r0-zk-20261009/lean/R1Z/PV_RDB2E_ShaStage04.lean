import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 4; constants and bank operands checked by sha-stages.py. -/
def stage04 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank0 b).w4) (⟨0x240ca1cc,0x0fc19dc6,0xefbe4786,0xe49b69c1⟩)
  (join pair.1 pair.2,bank0 b)

theorem rounds_at_04 (s : S) (b : Banks) :
    (stage04 s b).1=four s (add ((bank0 b).w4) (⟨0x240ca1cc,0x0fc19dc6,0xefbe4786,0xe49b69c1⟩)) :=
  four_source s ((bank0 b).w4) (⟨0x240ca1cc,0x0fc19dc6,0xefbe4786,0xe49b69c1⟩)

theorem schedule_at_04 (b : Banks) :
    window1 (stage04 (join b.w0 b.w1) b).2 = advance (window0 b) := phase0 b

#print axioms rounds_at_04
#print axioms schedule_at_04
end R1Z.PV_RDB2E_ShaScalar
