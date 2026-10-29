import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 10; constants and bank operands checked by sha-stages.py. -/
def stage10 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank1 b).w0) (⟨0xc76c51a3,0xc24b8b70,0xa81a664b,0xa2bfe8a1⟩)
  (join pair.1 pair.2,bank1 b)

theorem rounds_at_10 (s : S) (b : Banks) :
    (stage10 s b).1=four s (add ((bank1 b).w0) (⟨0xc76c51a3,0xc24b8b70,0xa81a664b,0xa2bfe8a1⟩)) :=
  four_source s ((bank1 b).w0) (⟨0xc76c51a3,0xc24b8b70,0xa81a664b,0xa2bfe8a1⟩)

theorem schedule_at_10 (b : Banks) :
    window2 (stage10 (join b.w0 b.w1) b).2 = advance (window1 b) := phase1 b

#print axioms rounds_at_10
#print axioms schedule_at_10
end R1Z.PV_RDB2E_ShaScalar
