import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 15; constants and bank operands checked by sha-stages.py. -/
def stage15 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank1 b).w0) (⟨0xc67178f2,0xbef9a3f7,0xa4506ceb,0x90befffa⟩)
  (join pair.1 pair.2,bank1 b)

theorem rounds_at_15 (s : S) (b : Banks) :
    (stage15 s b).1=four s (add ((bank1 b).w0) (⟨0xc67178f2,0xbef9a3f7,0xa4506ceb,0x90befffa⟩)) :=
  four_source s ((bank1 b).w0) (⟨0xc67178f2,0xbef9a3f7,0xa4506ceb,0x90befffa⟩)

theorem schedule_at_15 (b : Banks) :
    window2 (stage15 (join b.w0 b.w1) b).2 = advance (window1 b) := phase1 b

#print axioms rounds_at_15
#print axioms schedule_at_15
end R1Z.PV_RDB2E_ShaScalar
