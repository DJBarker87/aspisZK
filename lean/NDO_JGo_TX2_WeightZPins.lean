import NDO_JGo_TX2_WeightRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightZPins
open Aeneas Aeneas.Std Result FIn_WeightsExtract JGo_TX2_WeightData

def back0 (row : Row) : Factors := Array.make 5#usize [r0_5,r1_5,r2_5,row,r4_0]
def back1 (row : Row) : Factors := Array.make 5#usize [r0_5,r1_5,r2_5,r3_5,row]

theorem read0 : Array.index_mut_usize factors15 3#usize=ok (r3_0,back0) := by rfl
#print axioms read0
theorem read1 : Array.index_mut_usize factors20 4#usize=ok (r4_0,back1) := by rfl
#print axioms read1

theorem write0 : Array.update r3_0 0#usize
    (Array.make 4#usize [field.QM31.ONE,z0y,z0x,z0product])=ok r3_1 := by with_unfolding_all rfl
#print axioms write0
theorem write1 : Array.update r4_0 0#usize
    (Array.make 4#usize [field.QM31.ONE,z1y,z1x,z1product])=ok r4_1 := by with_unfolding_all rfl
#print axioms write1

theorem back0_pin : back0 r3_1=factors16 := by rfl
#print axioms back0_pin
theorem back1_pin : back1 r4_1=factors21 := by rfl
#print axioms back1_pin
end AspisR1.JGo_TX2_WeightZPins
end
