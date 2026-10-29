import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 13; constants and bank operands checked by sha-stages.py. -/
def stage13 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank4 b).w3) (⟨0x682e6ff3,0x5b9cca4f,0x4ed8aa4a,0x391c0cb3⟩)
  (join pair.1 pair.2,bank4 b)

theorem rounds_at_13 (s : S) (b : Banks) :
    (stage13 s b).1=four s (add ((bank4 b).w3) (⟨0x682e6ff3,0x5b9cca4f,0x4ed8aa4a,0x391c0cb3⟩)) :=
  four_source s ((bank4 b).w3) (⟨0x682e6ff3,0x5b9cca4f,0x4ed8aa4a,0x391c0cb3⟩)

theorem schedule_at_13 (b : Banks) :
    window0 (stage13 (join b.w0 b.w1) b).2 = advance (window4 b) := phase4 b

#print axioms rounds_at_13
#print axioms schedule_at_13
end R1Z.PV_RDB2E_ShaScalar
