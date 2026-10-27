import XRp_SamplerSeed
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_SeedArray
open XRp_SamplerSeed XRp_DivisionWitness AspisR1.AdapterRw.Scalar
abbrev fn := XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32

theorem list_seed : core.array.fromFnList fn 8 0#usize block = ok (rank.val,block) := by
  have h0 : word block 0#usize = ok (2147483647#u32,block) := word0
  have h1 : word block 1#usize = ok (0#u32,block) := word1
  have h2 : word block 2#usize = ok (0#u32,block) := word2
  have h3 : word block 3#usize = ok (0#u32,block) := word3
  have h4 : word block 4#usize = ok (0#u32,block) := word4
  have h5 : word block 5#usize = ok (0#u32,block) := word5
  have h6 : word block 6#usize = ok (0#u32,block) := word6
  have h7 : word block 7#usize = ok (0#u32,block) := word7
  have a0 : 0#usize + 1#usize = ok 1#usize := add_eq _ _ _ rfl
  have a1 : 1#usize + 1#usize = ok 2#usize := add_eq _ _ _ rfl
  have a2 : 2#usize + 1#usize = ok 3#usize := add_eq _ _ _ rfl
  have a3 : 3#usize + 1#usize = ok 4#usize := add_eq _ _ _ rfl
  have a4 : 4#usize + 1#usize = ok 5#usize := add_eq _ _ _ rfl
  have a5 : 5#usize + 1#usize = ok 6#usize := add_eq _ _ _ rfl
  have a6 : 6#usize + 1#usize = ok 7#usize := add_eq _ _ _ rfl
  simp only [core.array.fromFnList, h0,h1,h2,h3,h4,h5,h6,h7,a0,a1,a2,a3,a4,a5,a6,bind_tc_ok]
  all_goals rfl

theorem init : core.array.from_fn 8#usize fn block = ok rank := by
  change (match core.array.fromFnList fn 8 0#usize block with
    | .fail e => Result.fail e
    | .div => Result.div
    | .ok (xs,_) => if h : xs.length = 8 then Result.ok (⟨xs,h⟩ : Array U32 8#usize) else Result.fail .panic) = _
  rw [list_seed]
  rfl

#print axioms list_seed
#print axioms init
end XRp_SeedArray
