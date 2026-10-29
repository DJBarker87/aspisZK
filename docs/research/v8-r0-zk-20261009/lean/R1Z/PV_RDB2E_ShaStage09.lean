import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 9; constants and bank operands checked by sha-stages.py. -/
def stage09 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank0 b).w4) (⟨0x92722c85,0x81c2c92e,0x766a0abb,0x650a7354⟩)
  (join pair.1 pair.2,bank0 b)

theorem rounds_at_09 (s : S) (b : Banks) :
    (stage09 s b).1=four s (add ((bank0 b).w4) (⟨0x92722c85,0x81c2c92e,0x766a0abb,0x650a7354⟩)) :=
  four_source s ((bank0 b).w4) (⟨0x92722c85,0x81c2c92e,0x766a0abb,0x650a7354⟩)

theorem schedule_at_09 (b : Banks) :
    window1 (stage09 (join b.w0 b.w1) b).2 = advance (window0 b) := phase0 b

#print axioms rounds_at_09
#print axioms schedule_at_09
end R1Z.PV_RDB2E_ShaScalar
