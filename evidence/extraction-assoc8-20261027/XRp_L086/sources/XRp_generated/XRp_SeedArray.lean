import XRp_SamplerSeed
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_SeedArray
open XRp_SamplerSeed XRp_DivisionWitness AspisR1.AdapterRw.Scalar
abbrev fn := XRn_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32


theorem suffix7 : core.array.fromFnList fn 1 7#usize block = ok (List.replicate 1 0#u32,block) := by
  rw [core.array.fromFnList]
  change (do let (v,c) ← word block 7#usize; ok ([v],c)) = _
  rw [word7]
  rfl
#print axioms suffix7

theorem suffix6 : core.array.fromFnList fn 2 6#usize block = ok (List.replicate 2 0#u32,block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 6#usize
    let j ← 6#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 1 j c
    ok (v::xs,c')) = _
  rw [word6]
  change (do
    let j ← 6#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 1 j block
    ok (0#u32::xs,c')) = _
  have ha : 6#usize + 1#usize = ok 7#usize := add_eq _ _ _ rfl
  rw [ha]
  change (do let (xs,c') ← core.array.fromFnList fn 1 7#usize block
             ok (0#u32::xs,c')) = _
  rw [suffix7]
  rfl
#print axioms suffix6

theorem suffix5 : core.array.fromFnList fn 3 5#usize block = ok (List.replicate 3 0#u32,block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 5#usize
    let j ← 5#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 2 j c
    ok (v::xs,c')) = _
  rw [word5]
  change (do
    let j ← 5#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 2 j block
    ok (0#u32::xs,c')) = _
  have ha : 5#usize + 1#usize = ok 6#usize := add_eq _ _ _ rfl
  rw [ha]
  change (do let (xs,c') ← core.array.fromFnList fn 2 6#usize block
             ok (0#u32::xs,c')) = _
  rw [suffix6]
  rfl
#print axioms suffix5

theorem suffix4 : core.array.fromFnList fn 4 4#usize block = ok (List.replicate 4 0#u32,block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 4#usize
    let j ← 4#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 3 j c
    ok (v::xs,c')) = _
  rw [word4]
  change (do
    let j ← 4#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 3 j block
    ok (0#u32::xs,c')) = _
  have ha : 4#usize + 1#usize = ok 5#usize := add_eq _ _ _ rfl
  rw [ha]
  change (do let (xs,c') ← core.array.fromFnList fn 3 5#usize block
             ok (0#u32::xs,c')) = _
  rw [suffix5]
  rfl
#print axioms suffix4

theorem suffix3 : core.array.fromFnList fn 5 3#usize block = ok (List.replicate 5 0#u32,block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 3#usize
    let j ← 3#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 4 j c
    ok (v::xs,c')) = _
  rw [word3]
  change (do
    let j ← 3#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 4 j block
    ok (0#u32::xs,c')) = _
  have ha : 3#usize + 1#usize = ok 4#usize := add_eq _ _ _ rfl
  rw [ha]
  change (do let (xs,c') ← core.array.fromFnList fn 4 4#usize block
             ok (0#u32::xs,c')) = _
  rw [suffix4]
  rfl
#print axioms suffix3

theorem suffix2 : core.array.fromFnList fn 6 2#usize block = ok (List.replicate 6 0#u32,block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 2#usize
    let j ← 2#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 5 j c
    ok (v::xs,c')) = _
  rw [word2]
  change (do
    let j ← 2#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 5 j block
    ok (0#u32::xs,c')) = _
  have ha : 2#usize + 1#usize = ok 3#usize := add_eq _ _ _ rfl
  rw [ha]
  change (do let (xs,c') ← core.array.fromFnList fn 5 3#usize block
             ok (0#u32::xs,c')) = _
  rw [suffix3]
  rfl
#print axioms suffix2

theorem suffix1 : core.array.fromFnList fn 7 1#usize block = ok (List.replicate 7 0#u32,block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 1#usize
    let j ← 1#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 6 j c
    ok (v::xs,c')) = _
  rw [word1]
  change (do
    let j ← 1#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 6 j block
    ok (0#u32::xs,c')) = _
  have ha : 1#usize + 1#usize = ok 2#usize := add_eq _ _ _ rfl
  rw [ha]
  change (do let (xs,c') ← core.array.fromFnList fn 6 2#usize block
             ok (0#u32::xs,c')) = _
  rw [suffix2]
  rfl
#print axioms suffix1

theorem suffix0 : core.array.fromFnList fn 8 0#usize block = ok (XRp_DivisionWitness.rank.val,block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 0#usize
    let j ← 0#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 7 j c
    ok (v::xs,c')) = _
  rw [word0]
  change (do
    let j ← 0#usize + 1#usize
    let (xs,c') ← core.array.fromFnList fn 7 j block
    ok (2147483647#u32::xs,c')) = _
  have ha : 0#usize + 1#usize = ok 1#usize := add_eq _ _ _ rfl
  rw [ha]
  change (do let (xs,c') ← core.array.fromFnList fn 7 1#usize block
             ok (2147483647#u32::xs,c')) = _
  rw [suffix1]
  rfl
#print axioms suffix0

theorem list_seed : core.array.fromFnList fn 8 0#usize block = ok (rank.val,block) := suffix0

theorem init : _root_.core.array.from_fn 8#usize fn block = ok rank := by
  have h8 : (8#usize).val = 8 := by scalar_tac
  unfold _root_.core.array.from_fn
  have hs : core.array.fromFnList fn (8#usize).val 0#usize block = ok (rank.val,block) := by
    simpa only [h8] using list_seed
  rw [hs]
  change (if h : rank.val.length = (8#usize).val then ok (⟨rank.val,h⟩ : Array U32 8#usize) else fail .panic) = _
  rw [dif_pos rank.property]

#print axioms list_seed
#print axioms init
end XRp_SeedArray
