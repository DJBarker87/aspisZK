import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 11; constants and bank operands checked by sha-stages.py. -/
def stage11 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank2 b).w1) (⟨0x106aa070,0xf40e3585,0xd6990624,0xd192e819⟩)
  (join pair.1 pair.2,bank2 b)

theorem rounds_at_11 (s : S) (b : Banks) :
    (stage11 s b).1=four s (add ((bank2 b).w1) (⟨0x106aa070,0xf40e3585,0xd6990624,0xd192e819⟩)) :=
  four_source s ((bank2 b).w1) (⟨0x106aa070,0xf40e3585,0xd6990624,0xd192e819⟩)

theorem schedule_at_11 (b : Banks) :
    window3 (stage11 (join b.w0 b.w1) b).2 = advance (window2 b) := phase2 b

#print axioms rounds_at_11
#print axioms schedule_at_11
end R1Z.PV_RDB2E_ShaScalar
