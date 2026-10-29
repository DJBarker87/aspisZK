import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 3; constants and bank operands checked by sha-stages.py. -/
def stage03 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) (b.w3) (⟨0xc19bf174,0x9bdc06a7,0x80deb1fe,0x72be5d74⟩)
  (join pair.1 pair.2,b)

theorem rounds_at_03 (s : S) (b : Banks) :
    (stage03 s b).1=four s (add (b.w3) (⟨0xc19bf174,0x9bdc06a7,0x80deb1fe,0x72be5d74⟩)) :=
  four_source s (b.w3) (⟨0xc19bf174,0x9bdc06a7,0x80deb1fe,0x72be5d74⟩)

#print axioms rounds_at_03
end R1Z.PV_RDB2E_ShaScalar
