import CuSavingsRetainedCompositionDotsPrefixSource

/-! Continuation form of the common complete emitted slot computation.
Both source callbacks are checked equal to this factorization, rather than
assuming that their final capture values can be erased. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.CuSavingsRetainedCompositionPrefixSlot
open Aeneas Aeneas.Std Result AspisR1RetainedDots
open CuSavingsArrayBuilder
variable [Shared]

def run {A : Type} (s : Slice U8) (a : Array field.wide_exact.WideExact 29#usize)
    (slot : Usize) (k : field.wide_exact.WideExact → Result A) : Result A := do
  let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    {start := 0#usize,«end» := 26#usize} 4#usize
  let limbs1 ←
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      iter s a slot (Array.repeat 8#usize 0#u64)
  let a1 ← core.array.from_fn 8#usize
    new_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 limbs1
  let o ← field.wide_exact.WideExact.from_limbs a1
  let value ← core.option.Option.unwrap o
  let tail ← fast_pairing.EbyKDot.new
  let we ← Array.index_usize a 28#usize
  let i ← slot * 120#usize
  let i1 ← i + 104#usize
  let i2 ← i + 120#usize
  let s1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    s {start := i1,«end» := i2}
  let o1 ← field.QM31.from_le_bytes s1
  let q ← core.option.Option.unwrap o1
  let (r,tail1) ← fast_pairing.EbyKDot.push tail we q
  core.result.Result.unwrap core.fmt.DebugUnit r
  let tail2 ←
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
      {start := 0#usize,«end» := 2#usize} s a slot tail1
  let we1 ← fast_pairing.EbyKDot.finish tail2
  let we2 ← field.wide_exact.WideExact.add value we1
  k we2

theorem old_factor (s : Slice U8) (a : Array field.wide_exact.WideExact 29#usize)
    (slot : Usize) :
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (s,a) slot = run s a slot (fun value => .ok (value,(s,a))) := by
  rfl

theorem new_factor (s : Array U8 608#usize)
    (a : Array field.wide_exact.WideExact 29#usize) (slot : Usize) :
    prefix_new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (s,a) slot = run s.to_slice a slot (fun value => .ok (value,(s,a))) := by
  rfl

omit [Shared] in
private theorem remap_bind {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) :
    remap f (r >>= k) = (do let x ← r;remap f (k x)) := by
  cases r <;> rfl

theorem naturality {A B : Type} (f : A → B) (s : Slice U8)
    (a : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (k : field.wide_exact.WideExact → Result A) :
    remap f (run s a slot k) = run s a slot (fun value => remap f (k value)) := by
  unfold run
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value1 h1
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value2 h2
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value3 h3
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value4 h4
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value5 h5
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value6 h6
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value7 h7
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value8 h8
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value9 h9
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value10 h10
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value11 h11
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value12 h12
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value13 h13
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value14 h14
  rcases value14 with ⟨r,tail1⟩
  change remap f (do
      core.result.Result.unwrap core.fmt.DebugUnit r
      let tail2 ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
        {start := 0#usize,«end» := 2#usize} s a slot tail1
      let we1 ← fast_pairing.EbyKDot.finish tail2
      let we2 ← field.wide_exact.WideExact.add value5 we1
      k we2) = (do
      core.result.Result.unwrap core.fmt.DebugUnit r
      let tail2 ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
        {start := 0#usize,«end» := 2#usize} s a slot tail1
      let we1 ← fast_pairing.EbyKDot.finish tail2
      let we2 ← field.wide_exact.WideExact.add value5 we1
      remap f (k we2))
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value15 h15
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value16 h16
  rw [remap_bind]
  apply (bind_eq_iff _ _ _).mpr
  intro value17 h17
  rw [remap_bind]

#print axioms old_factor
#print axioms new_factor
#print axioms naturality
end AspisR1.CuSavingsRetainedCompositionPrefixSlot
