import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 6; constants and bank operands checked by sha-stages.py. -/
def stage06 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank2 b).w1) (⟨0xbf597fc7,0xb00327c8,0xa831c66d,0x983e5152⟩)
  (join pair.1 pair.2,bank2 b)

theorem rounds_at_06 (s : S) (b : Banks) :
    (stage06 s b).1=four s (add ((bank2 b).w1) (⟨0xbf597fc7,0xb00327c8,0xa831c66d,0x983e5152⟩)) :=
  four_source s ((bank2 b).w1) (⟨0xbf597fc7,0xb00327c8,0xa831c66d,0x983e5152⟩)

theorem schedule_at_06 (b : Banks) :
    window3 (stage06 (join b.w0 b.w1) b).2 = advance (window2 b) := phase2 b

#print axioms rounds_at_06
#print axioms schedule_at_06
end R1Z.PV_RDB2E_ShaScalar
