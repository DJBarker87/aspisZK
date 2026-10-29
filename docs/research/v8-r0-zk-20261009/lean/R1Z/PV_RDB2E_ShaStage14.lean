import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 14; constants and bank operands checked by sha-stages.py. -/
def stage14 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank0 b).w4) (⟨0x8cc70208,0x84c87814,0x78a5636f,0x748f82ee⟩)
  (join pair.1 pair.2,bank0 b)

theorem rounds_at_14 (s : S) (b : Banks) :
    (stage14 s b).1=four s (add ((bank0 b).w4) (⟨0x8cc70208,0x84c87814,0x78a5636f,0x748f82ee⟩)) :=
  four_source s ((bank0 b).w4) (⟨0x8cc70208,0x84c87814,0x78a5636f,0x748f82ee⟩)

theorem schedule_at_14 (b : Banks) :
    window1 (stage14 (join b.w0 b.w1) b).2 = advance (window0 b) := phase0 b

#print axioms rounds_at_14
#print axioms schedule_at_14
end R1Z.PV_RDB2E_ShaScalar
