import PV_B3P_DirectMaskBridge17227
namespace PV_B3P_MaskSource542227
open Aeneas Aeneas.Std PV_B3P_Direct17227
set_option autoImplicit false

/-- Mathematical ctpop specification. Compiler implementation is V370,
D381/D386, not a new native axiom or trust-list field. -/
def ctpop16_spec542 (bits : BitVec 16) : BitVec 32 := bits.cpop.zeroExtend 32
/-- Mathematical cttz specification, including zero -> 16 (not cttz_nonzero).
Compiler implementation is retained V370 / D381,D386. -/
def cttz16_spec542 (bits : BitVec 16) : BitVec 32 := bits.ctz.zeroExtend 32

/-- Exact ordinary source wrapper: return intrinsics::ctpop(self). -/
def count_ones_source542 (value : U16) : Result U32 := .ok ⟨ctpop16_spec542 value.bv⟩
/-- Exact ordinary source wrapper: return intrinsics::cttz(self). -/
def trailing_zeros_source542 (value : U16) : Result U32 := .ok ⟨cttz16_spec542 value.bv⟩

theorem count_ones_source_step542 (value : U16) :
    count_ones_source542 value = .ok ⟨ctpop16_spec542 value.bv⟩ := rfl
theorem trailing_zeros_source_step542 (value : U16) :
    trailing_zeros_source542 value = .ok ⟨cttz16_spec542 value.bv⟩ := rfl

-- Every cell is at most sixteen bits, with a reduction graph bounded by 16.
-- These are intrinsic specification equations, never a field/range replay.
theorem count_1749_source542 : count_ones_source542 1749#u16 = .ok 7#u32 := by rfl
theorem count_2048_source542 : count_ones_source542 2048#u16 = .ok 1#u32 := by rfl
theorem count_2049_source542 : count_ones_source542 2049#u16 = .ok 2#u32 := by rfl
theorem count_4097_source542 : count_ones_source542 4097#u16 = .ok 2#u32 := by rfl
theorem count_6144_source542 : count_ones_source542 6144#u16 = .ok 2#u32 := by rfl
theorem count_6145_source542 : count_ones_source542 6145#u16 = .ok 3#u32 := by rfl
theorem count_26214_source542 : count_ones_source542 26214#u16 = .ok 8#u32 := by rfl
theorem trail_1024_source542 : trailing_zeros_source542 1024#u16 = .ok 10#u32 := by rfl
theorem trail_1536_source542 : trailing_zeros_source542 1536#u16 = .ok 9#u32 := by rfl
theorem trail_1664_source542 : trailing_zeros_source542 1664#u16 = .ok 7#u32 := by rfl
theorem trail_1728_source542 : trailing_zeros_source542 1728#u16 = .ok 6#u32 := by rfl
theorem trail_1744_source542 : trailing_zeros_source542 1744#u16 = .ok 4#u32 := by rfl
theorem trail_1748_source542 : trailing_zeros_source542 1748#u16 = .ok 2#u32 := by rfl
theorem trail_1749_source542 : trailing_zeros_source542 1749#u16 = .ok 0#u32 := by rfl
theorem trail_2048_source542 : trailing_zeros_source542 2048#u16 = .ok 11#u32 := by rfl
theorem trail_2049_source542 : trailing_zeros_source542 2049#u16 = .ok 0#u32 := by rfl
theorem trail_4096_source542 : trailing_zeros_source542 4096#u16 = .ok 12#u32 := by rfl
theorem trail_4097_source542 : trailing_zeros_source542 4097#u16 = .ok 0#u32 := by rfl
theorem trail_6144_source542 : trailing_zeros_source542 6144#u16 = .ok 11#u32 := by rfl
theorem trail_6145_source542 : trailing_zeros_source542 6145#u16 = .ok 0#u32 := by rfl
theorem trail_16384_source542 : trailing_zeros_source542 16384#u16 = .ok 14#u32 := by rfl
theorem trail_24576_source542 : trailing_zeros_source542 24576#u16 = .ok 13#u32 := by rfl
theorem trail_25600_source542 : trailing_zeros_source542 25600#u16 = .ok 10#u32 := by rfl
theorem trail_26112_source542 : trailing_zeros_source542 26112#u16 = .ok 9#u32 := by rfl
theorem trail_26176_source542 : trailing_zeros_source542 26176#u16 = .ok 6#u32 := by rfl
theorem trail_26208_source542 : trailing_zeros_source542 26208#u16 = .ok 5#u32 := by rfl
theorem trail_26212_source542 : trailing_zeros_source542 26212#u16 = .ok 2#u32 := by rfl
theorem trail_26214_source542 : trailing_zeros_source542 26214#u16 = .ok 1#u32 := by rfl

theorem count_zero_source542 : count_ones_source542 0#u16 = .ok 0#u32 := rfl
theorem trailing_zero_source542 : trailing_zeros_source542 0#u16 = .ok 16#u32 := rfl

theorem mask_integer_source_laws542 :
    MaskIntegerLaws17 count_ones_source542 trailing_zeros_source542 := by
  exact ⟨count_1749_source542,count_2048_source542,count_2049_source542,count_4097_source542,count_6144_source542,count_6145_source542,count_26214_source542,trail_1024_source542,trail_1536_source542,trail_1664_source542,trail_1728_source542,trail_1744_source542,trail_1748_source542,trail_1749_source542,trail_2048_source542,trail_2049_source542,trail_4096_source542,trail_4097_source542,trail_6144_source542,trail_6145_source542,trail_16384_source542,trail_24576_source542,trail_25600_source542,trail_26112_source542,trail_26176_source542,trail_26208_source542,trail_26212_source542,trail_26214_source542⟩

#print axioms count_ones_source_step542
#print axioms trailing_zeros_source_step542
#print axioms count_zero_source542
#print axioms trailing_zero_source542
#print axioms mask_integer_source_laws542
end PV_B3P_MaskSource542227
