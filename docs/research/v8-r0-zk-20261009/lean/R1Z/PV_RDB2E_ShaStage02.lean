import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 2; constants and bank operands checked by sha-stages.py. -/
def stage02 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) (b.w2) (⟨0x550c7dc3,0x243185be,0x12835b01,0xd807aa98⟩)
  (join pair.1 pair.2,b)

theorem rounds_at_02 (s : S) (b : Banks) :
    (stage02 s b).1=four s (add (b.w2) (⟨0x550c7dc3,0x243185be,0x12835b01,0xd807aa98⟩)) :=
  four_source s (b.w2) (⟨0x550c7dc3,0x243185be,0x12835b01,0xd807aa98⟩)

#print axioms rounds_at_02
end R1Z.PV_RDB2E_ShaScalar
