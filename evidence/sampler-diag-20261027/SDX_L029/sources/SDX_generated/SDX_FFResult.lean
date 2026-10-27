import SDX_FF
import AdapterRwScalar
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace SDX_FFResult
open SDX_Common SDX_FF AspisR1.AdapterRw.Scalar

def block : Array U8 32#usize := ⟨[255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8],by simp⟩
def rank : Array U32 8#usize := ⟨[4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32],by simp⟩
def digits : Array U32 8#usize := ⟨List.replicate 8 255#u32,by simp⟩
abbrev word := SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
abbrev seedFn := SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
abbrev callback := SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
abbrev fn := SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32

theorem word0 : word block 0#usize = ok (4294967295#u32,block) := by
  unfold word SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 0#usize = ok 0#usize := mul_eq _ _ _ rfl
  have ha : 0#usize + 4#usize = ok 4#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word0

theorem word1 : word block 1#usize = ok (4294967295#u32,block) := by
  unfold word SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 1#usize = ok 4#usize := mul_eq _ _ _ rfl
  have ha : 4#usize + 4#usize = ok 8#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word1

theorem word2 : word block 2#usize = ok (4294967295#u32,block) := by
  unfold word SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 2#usize = ok 8#usize := mul_eq _ _ _ rfl
  have ha : 8#usize + 4#usize = ok 12#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word2

theorem word3 : word block 3#usize = ok (4294967295#u32,block) := by
  unfold word SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 3#usize = ok 12#usize := mul_eq _ _ _ rfl
  have ha : 12#usize + 4#usize = ok 16#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word3

theorem word4 : word block 4#usize = ok (4294967295#u32,block) := by
  unfold word SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 4#usize = ok 16#usize := mul_eq _ _ _ rfl
  have ha : 16#usize + 4#usize = ok 20#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word4

theorem word5 : word block 5#usize = ok (4294967295#u32,block) := by
  unfold word SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 5#usize = ok 20#usize := mul_eq _ _ _ rfl
  have ha : 20#usize + 4#usize = ok 24#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word5

theorem word6 : word block 6#usize = ok (4294967295#u32,block) := by
  unfold word SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 6#usize = ok 24#usize := mul_eq _ _ _ rfl
  have ha : 24#usize + 4#usize = ok 28#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word6

theorem word7 : word block 7#usize = ok (4294967295#u32,block) := by
  unfold word SDX_Join_Release.sampler.low_base_p_digits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have hm : 4#usize * 7#usize = ok 28#usize := mul_eq _ _ _ rfl
  have ha : 28#usize + 4#usize = ok 32#usize := add_eq _ _ _ rfl
  rw [hm,bind_tc_ok,ha,bind_tc_ok]
  rfl
#print axioms word7

theorem seed7 : core.array.fromFnList seedFn 1 7#usize block = ok ([4294967295#u32],block) := by
  rw [core.array.fromFnList]
  change (do let (v,c) ← word block 7#usize; ok ([v],c)) = _
  rw [word7]
  rfl
#print axioms seed7

theorem seed6 : core.array.fromFnList seedFn 2 6#usize block = ok ([4294967295#u32,4294967295#u32],block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 6#usize
    let j ← 6#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 1 j c
    ok (v::xs,c')) = _
  rw [word6]
  change (do
    let j ← 6#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 1 j block
    ok (4294967295#u32::xs,c')) = _
  have ha : 6#usize + 1#usize = ok 7#usize := add_eq _ _ _ rfl
  rw [ha,bind_tc_ok,seed7]
  rfl
#print axioms seed6

theorem seed5 : core.array.fromFnList seedFn 3 5#usize block = ok ([4294967295#u32,4294967295#u32,4294967295#u32],block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 5#usize
    let j ← 5#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 2 j c
    ok (v::xs,c')) = _
  rw [word5]
  change (do
    let j ← 5#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 2 j block
    ok (4294967295#u32::xs,c')) = _
  have ha : 5#usize + 1#usize = ok 6#usize := add_eq _ _ _ rfl
  rw [ha,bind_tc_ok,seed6]
  rfl
#print axioms seed5

theorem seed4 : core.array.fromFnList seedFn 4 4#usize block = ok ([4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32],block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 4#usize
    let j ← 4#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 3 j c
    ok (v::xs,c')) = _
  rw [word4]
  change (do
    let j ← 4#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 3 j block
    ok (4294967295#u32::xs,c')) = _
  have ha : 4#usize + 1#usize = ok 5#usize := add_eq _ _ _ rfl
  rw [ha,bind_tc_ok,seed5]
  rfl
#print axioms seed4

theorem seed3 : core.array.fromFnList seedFn 5 3#usize block = ok ([4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32],block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 3#usize
    let j ← 3#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 4 j c
    ok (v::xs,c')) = _
  rw [word3]
  change (do
    let j ← 3#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 4 j block
    ok (4294967295#u32::xs,c')) = _
  have ha : 3#usize + 1#usize = ok 4#usize := add_eq _ _ _ rfl
  rw [ha,bind_tc_ok,seed4]
  rfl
#print axioms seed3

theorem seed2 : core.array.fromFnList seedFn 6 2#usize block = ok ([4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32],block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 2#usize
    let j ← 2#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 5 j c
    ok (v::xs,c')) = _
  rw [word2]
  change (do
    let j ← 2#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 5 j block
    ok (4294967295#u32::xs,c')) = _
  have ha : 2#usize + 1#usize = ok 3#usize := add_eq _ _ _ rfl
  rw [ha,bind_tc_ok,seed3]
  rfl
#print axioms seed2

theorem seed1 : core.array.fromFnList seedFn 7 1#usize block = ok ([4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32],block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 1#usize
    let j ← 1#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 6 j c
    ok (v::xs,c')) = _
  rw [word1]
  change (do
    let j ← 1#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 6 j block
    ok (4294967295#u32::xs,c')) = _
  have ha : 1#usize + 1#usize = ok 2#usize := add_eq _ _ _ rfl
  rw [ha,bind_tc_ok,seed2]
  rfl
#print axioms seed1

theorem seed0 : core.array.fromFnList seedFn 8 0#usize block = ok ([4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32,4294967295#u32],block) := by
  rw [core.array.fromFnList]
  change (do
    let (v,c) ← word block 0#usize
    let j ← 0#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 7 j c
    ok (v::xs,c')) = _
  rw [word0]
  change (do
    let j ← 0#usize + 1#usize
    let (xs,c') ← core.array.fromFnList seedFn 7 j block
    ok (4294967295#u32::xs,c')) = _
  have ha : 0#usize + 1#usize = ok 1#usize := add_eq _ _ _ rfl
  rw [ha,bind_tc_ok,seed1]
  rfl
#print axioms seed0

theorem init : _root_.core.array.from_fn 8#usize seedFn block = ok rank := by
  have h8 : (8#usize).val = 8 := by scalar_tac
  unfold _root_.core.array.from_fn
  have hs : core.array.fromFnList seedFn (8#usize).val 0#usize block = ok (rank.val,block) := by
    simpa only [h8,rank] using seed0
  rw [hs]
  change (if h : rank.val.length = (8#usize).val then ok (⟨rank.val,h⟩ : Array U32 8#usize) else fail .panic) = _
  rw [dif_pos rank.property]
  rfl
#print axioms init

theorem division (i : Usize) : callback rank i = ok (255#u32,rank,id) := by
  unfold callback SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  change (do
    let (rem,back) ← loop step (st8,id,0#u64)
    let d ← lift (UScalar.cast .U32 rem)
    ok (d,Array.from_slice rank (back st8).iter.slice,id)) = _
  rw [loop8]
  change ok (255#u32,Array.from_slice rank ((fin8 id) st8).iter.slice,id) = _
  have h9 : 9 ≤ Usize.max := by scalar_tac
  have h10 : 10 ≤ Usize.max := by scalar_tac
  have h11 : 11 ≤ Usize.max := by scalar_tac
  have h12 : 12 ≤ Usize.max := by scalar_tac
  have h13 : 13 ≤ Usize.max := by scalar_tac
  have h14 : 14 ≤ Usize.max := by scalar_tac
  have h15 : 15 ≤ Usize.max := by scalar_tac
  have h16 : 16 ≤ Usize.max := by scalar_tac
  simp [fin0,fin1,fin2,fin3,fin4,fin5,fin6,fin7,fin8,st0,st1,st2,st3,st4,st5,st6,st7,st8,restore,mk,rank,Array.from_slice,h9,h10,h11,h12,h13,h14,h15,h16]
#print axioms division

theorem callback_state (i : Usize) : fn.call_mut rank i = ok (255#u32,rank) := by
  unfold fn SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  change (do let (v,c,restore) ← callback rank i; ok (v,restore c)) = _
  rw [division i]
  rfl
#print axioms callback_state

theorem eight_digits : SDX_Join_fromFnState 8#usize fn rank = ok (digits,rank) := by
  have h := constant fn rank 255#u32 callback_state 8 0#usize (by scalar_tac)
  unfold SDX_Join_fromFnState
  change (do
    let (xs,c) ← core.array.fromFnList fn 8 0#usize rank
    dite (xs.length = 8) (fun h => ok ((⟨xs,h⟩ : Array U32 8#usize),c)) (fun _ => fail .panic)) = _
  rw [h]
  rfl
#print axioms eight_digits

theorem emitted : SDX_Join_Release.sampler.low_base_p_digits block = ok (digits,4294967295#u32) := by
  unfold SDX_Join_Release.sampler.low_base_p_digits
  rw [init]
  change (do
    let (ds,c) ← SDX_Join_fromFnState 8#usize fn rank
    let q ← Array.index_usize c 0#usize
    ok (ds,q)) = _
  rw [eight_digits]
  rfl
#print axioms emitted
end SDX_FFResult
