import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 1; constants and bank operands checked by sha-stages.py. -/
def stage01 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) (b.w1) (⟨0xab1c5ed5,0x923f82a4,0x59f111f1,0x3956c25b⟩)
  (join pair.1 pair.2,b)

theorem rounds_at_01 (s : S) (b : Banks) :
    (stage01 s b).1=four s (add (b.w1) (⟨0xab1c5ed5,0x923f82a4,0x59f111f1,0x3956c25b⟩)) :=
  four_source s (b.w1) (⟨0xab1c5ed5,0x923f82a4,0x59f111f1,0x3956c25b⟩)

#print axioms rounds_at_01
end R1Z.PV_RDB2E_ShaScalar
