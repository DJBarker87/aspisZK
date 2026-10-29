import PV_B3P_Shift227
namespace PV_B3P_ShiftPorts227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem shift10_value : (10#i32).val=Int.ofNat (10#u32).val := rfl
theorem shift20_value : (20#i32).val=Int.ofNat (20#u32).val := rfl

theorem usize_u32_small (x : Usize) (h : x.val<64) :
    (UScalar.cast .U32 x).val=x.val := by
  simp only [UScalar.cast_val_eq]
  scalar_tac

theorem usize_u32_mod64 (x : Usize) :
    (UScalar.cast .U32 x).val % 64=x.val % 64 := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_mod_of_dvd _ (by decide)

#print axioms shift10_value
#print axioms shift20_value
#print axioms usize_u32_small
#print axioms usize_u32_mod64

theorem count0_value : (0#usize).val=(0#u32).val := rfl
#print axioms count0_value
theorem count1_value : (1#usize).val=(1#u32).val := rfl
#print axioms count1_value
theorem count2_value : (2#usize).val=(2#u32).val := rfl
#print axioms count2_value
theorem count3_value : (3#usize).val=(3#u32).val := rfl
#print axioms count3_value
theorem count4_value : (4#usize).val=(4#u32).val := rfl
#print axioms count4_value
theorem count5_value : (5#usize).val=(5#u32).val := rfl
#print axioms count5_value
theorem count6_value : (6#usize).val=(6#u32).val := rfl
#print axioms count6_value
theorem count7_value : (7#usize).val=(7#u32).val := rfl
#print axioms count7_value
theorem count8_value : (8#usize).val=(8#u32).val := rfl
#print axioms count8_value
theorem count9_value : (9#usize).val=(9#u32).val := rfl
#print axioms count9_value
theorem count10_value : (10#usize).val=(10#u32).val := rfl
#print axioms count10_value
theorem count11_value : (11#usize).val=(11#u32).val := rfl
#print axioms count11_value
theorem count12_value : (12#usize).val=(12#u32).val := rfl
#print axioms count12_value
theorem count13_value : (13#usize).val=(13#u32).val := rfl
#print axioms count13_value
theorem count14_value : (14#usize).val=(14#u32).val := rfl
#print axioms count14_value
theorem count15_value : (15#usize).val=(15#u32).val := rfl
#print axioms count15_value
theorem count16_value : (16#usize).val=(16#u32).val := rfl
#print axioms count16_value
theorem count17_value : (17#usize).val=(17#u32).val := rfl
#print axioms count17_value
theorem count18_value : (18#usize).val=(18#u32).val := rfl
#print axioms count18_value
theorem count19_value : (19#usize).val=(19#u32).val := rfl
#print axioms count19_value

end PV_B3P_ShiftPorts227
