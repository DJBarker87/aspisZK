import R1Z.PV_RDB2E_ShaBanks
namespace R1Z.PV_RDB2E_ShaScalar
set_option autoImplicit false
/-- Exact source stage 5; constants and bank operands checked by sha-stages.py. -/
def stage05 (s : S) (b : Banks) : S × Banks :=
  let pair := rounds4 (abef s) (cdgh s) ((bank1 b).w0) (⟨0x76f988da,0x5cb0a9dc,0x4a7484aa,0x2de92c6f⟩)
  (join pair.1 pair.2,bank1 b)

theorem rounds_at_05 (s : S) (b : Banks) :
    (stage05 s b).1=four s (add ((bank1 b).w0) (⟨0x76f988da,0x5cb0a9dc,0x4a7484aa,0x2de92c6f⟩)) :=
  four_source s ((bank1 b).w0) (⟨0x76f988da,0x5cb0a9dc,0x4a7484aa,0x2de92c6f⟩)

theorem schedule_at_05 (b : Banks) :
    window2 (stage05 (join b.w0 b.w1) b).2 = advance (window1 b) := phase1 b

#print axioms rounds_at_05
#print axioms schedule_at_05
end R1Z.PV_RDB2E_ShaScalar
