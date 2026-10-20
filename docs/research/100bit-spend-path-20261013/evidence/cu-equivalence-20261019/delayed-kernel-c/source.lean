import CuSavingsDelayedBatches
import CuSavingsDelayedMaterialize
import CuSavingsArrayBuilderBounded
set_option autoImplicit false
namespace AspisR1.CuSavingsDelayedKernel
open Aeneas Aeneas.Std Result
open AspisR1DelayedDots AspisV8R17.RawReducer
open CuSavingsDelayedArrays CuSavingsDelayedIterator CuSavingsDelayedBatches
variable [Shared]

def suffix (c : old_dots.four_dots.closure) (tupled_args : Usize) (a1 : Canon) :
    Result (field.wide_exact.WideExact × old_dots.four_dots.closure) := do
  let (s,a) := c
  let o ← field.wide_exact.WideExact.from_limbs a1
  let value ← core.option.Option.unwrap o
  let tail ← fast_pairing.EbyKDot.new
  let we ← Array.index_usize a 28#usize
  let i ← tupled_args * 120#usize
  let i1 ← i + 104#usize
  let i2 ← i + 120#usize
  let s1 ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) s { start := i1, «end» := i2 }
  let o1 ← field.QM31.from_le_bytes s1
  let q ← core.option.Option.unwrap o1
  let (r, tail1) ← fast_pairing.EbyKDot.push tail we q
  core.result.Result.unwrap core.fmt.DebugUnit r
  let tail2 ←
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
      { start := 0#usize, «end» := 2#usize } s a tupled_args tail1
  let we1 ← fast_pairing.EbyKDot.finish tail2
  let we2 ← field.wide_exact.WideExact.add value we1
  ok (we2, c)

theorem old_factor (c : old_dots.four_dots.closure) (slot : Usize) :
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut c slot = (do
      let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start := 0#usize,«end» := 26#usize} 4#usize
      let limbs ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0 iter c.1 c.2 slot (Array.repeat 8#usize field.M31.ZERO)
      let a1 ← core.array.from_fn 8#usize
        old_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 limbs
      suffix c slot a1) := by
  rcases c with ⟨bytes,gamma⟩
  rfl

theorem new_factor (c : new_dots.four_dots.closure) (slot : Usize) :
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut c slot = (do
      let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start := 0#usize,«end» := 26#usize} 4#usize
      let limbs ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0 iter c.1 c.2 slot (Array.repeat 8#usize 0#u64)
      let a1 ← core.array.from_fn 8#usize
        new_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 limbs
      suffix c slot a1) := by
  rcases c with ⟨bytes,gamma⟩
  simp only [new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut,suffix,CuSavingsDelayedCommon.tail_eq]
  rfl

theorem zero_state : State 0 0 (Array.repeat 8#usize field.M31.ZERO) (Array.repeat 8#usize 0#u64) := by
  intro j
  have hz64 : wordAt (Array.repeat 8#usize 0#u64) j = 0#u64 := by
    change (List.replicate (8#usize).val (0#u64))[j.val] = _
    simp only [List.getElem_replicate]
  have hz32 : wordAt (Array.repeat 8#usize field.M31.ZERO) j = 0#u32 := by
    change (List.replicate (8#usize).val field.M31.ZERO)[j.val] = _
    simp only [List.getElem_replicate,field.M31.ZERO]
  simp only [hz64,hz32,Nat.not_lt_zero,↓reduceIte]
  constructor <;> decide

theorem slot_equivalence (c : new_dots.four_dots.closure) (slot : Usize) :
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut c slot =
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut c slot := by
  rw [old_factor,new_factor]
  obtain ⟨iter,hiter,hframe⟩ := WP.spec_imp_exists
    (core.iter.traits.iterator.Iterator.step_by.trait_default.spec
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      ({start := 0#usize,«end» := 26#usize} : core.ops.range.Range Usize)
      4#usize (by scalar_tac))
  rw [hiter,bind_tc_ok]
  have hi : At 0 iter := by
    rcases hframe with ⟨he,hs⟩
    simp only [At,he,hs]
    constructor <;> scalar_tac
  apply CuSavingsDelayedBatches.source_transport 7 0 iter c.1 c.2 slot
    (Array.repeat 8#usize field.M31.ZERO) (Array.repeat 8#usize 0#u64)
    (by omega) (by omega) hi zero_state
  intro old raw h
  rw [CuSavingsDelayedMaterialize.source_eq old raw h]

theorem source_equivalence (bytes : Slice U8) (gamma : Array field.wide_exact.WideExact 29#usize) :
    new_dots.four_dots bytes gamma = old_dots.four_dots bytes gamma := by
  unfold new_dots.four_dots old_dots.four_dots
  apply CuSavingsArrayBuilder.build_naturality _ _ id
  intro state index
  have heq := slot_equivalence state index
  have hmap := congrArg
    (CuSavingsArrayBuilder.remap (fun (value,state1) => (value,id state1))) heq
  have hid : ∀ r : Result (field.wide_exact.WideExact × old_dots.four_dots.closure),
      CuSavingsArrayBuilder.remap (fun (v,state1) => (v,id state1)) r = r := by
    intro r
    cases r with
    | fail e => rfl
    | div => rfl
    | ok pair => rcases pair with ⟨v,state1⟩;rfl
  exact hmap.trans (hid _)

#print axioms old_factor
#print axioms new_factor
#print axioms slot_equivalence
#print axioms source_equivalence
end AspisR1.CuSavingsDelayedKernel
