import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 0; constants and bank operands checked by sha-stages.py. -/
def stage00 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) (b.w0) (⟨0xe9b5dba5,0xb5c0fbcf,0x71374491,0x428a2f98⟩)
  (join pair.1 pair.2,b)

theorem rounds_at_00 (s : S) (b : Banks) :
    (stage00 s b).1=four s (add (b.w0) (⟨0xe9b5dba5,0xb5c0fbcf,0x71374491,0x428a2f98⟩)) :=
  four_source s (b.w0) (⟨0xe9b5dba5,0xb5c0fbcf,0x71374491,0x428a2f98⟩)

#print axioms rounds_at_00
end R1Z.PV_RDB2E_ShaScalar
