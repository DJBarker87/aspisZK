import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 7; constants and bank operands checked by sha-stages.py. -/
def stage07 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank3 b).w2) (⟨0x14292967,0x06ca6351,0xd5a79147,0xc6e00bf3⟩)
  (join pair.1 pair.2,bank3 b)

theorem rounds_at_07 (s : S) (b : Banks) :
    (stage07 s b).1=four s (add ((bank3 b).w2) (⟨0x14292967,0x06ca6351,0xd5a79147,0xc6e00bf3⟩)) :=
  four_source s ((bank3 b).w2) (⟨0x14292967,0x06ca6351,0xd5a79147,0xc6e00bf3⟩)

theorem schedule_at_07 (b : Banks) :
    window4 (stage07 (join b.w0 b.w1) b).2 = advance (window3 b) := phase3 b

#print axioms rounds_at_07
#print axioms schedule_at_07
end R1Z.PV_RDB2E_ShaScalar
