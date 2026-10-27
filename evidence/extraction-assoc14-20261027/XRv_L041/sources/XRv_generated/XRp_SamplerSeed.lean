import XRp_DivisionWitness
import AdapterRwScalar
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_SamplerSeed
open AspisR1.AdapterRw.Scalar

def block : Array U8 32#usize :=
  ⟨[255#u8,255#u8,255#u8,127#u8] ++ List.replicate 28 0#u8,by simp⟩
abbrev word := XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut

theorem word0 : word block 0#usize = ok (2147483647#u32,block) := by
  unfold word XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 0#usize = ok 0#usize := mul_eq _ _ _ rfl
  have ha : 0#usize + 4#usize = ok 4#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word0

theorem word1 : word block 1#usize = ok (0#u32,block) := by
  unfold word XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 1#usize = ok 4#usize := mul_eq _ _ _ rfl
  have ha : 4#usize + 4#usize = ok 8#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word1

theorem word2 : word block 2#usize = ok (0#u32,block) := by
  unfold word XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 2#usize = ok 8#usize := mul_eq _ _ _ rfl
  have ha : 8#usize + 4#usize = ok 12#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word2

theorem word3 : word block 3#usize = ok (0#u32,block) := by
  unfold word XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 3#usize = ok 12#usize := mul_eq _ _ _ rfl
  have ha : 12#usize + 4#usize = ok 16#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word3

theorem word4 : word block 4#usize = ok (0#u32,block) := by
  unfold word XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 4#usize = ok 16#usize := mul_eq _ _ _ rfl
  have ha : 16#usize + 4#usize = ok 20#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word4

theorem word5 : word block 5#usize = ok (0#u32,block) := by
  unfold word XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 5#usize = ok 20#usize := mul_eq _ _ _ rfl
  have ha : 20#usize + 4#usize = ok 24#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word5

theorem word6 : word block 6#usize = ok (0#u32,block) := by
  unfold word XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 6#usize = ok 24#usize := mul_eq _ _ _ rfl
  have ha : 24#usize + 4#usize = ok 28#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word6

theorem word7 : word block 7#usize = ok (0#u32,block) := by
  unfold word XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 7#usize = ok 28#usize := mul_eq _ _ _ rfl
  have ha : 28#usize + 4#usize = ok 32#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word7

end XRp_SamplerSeed
