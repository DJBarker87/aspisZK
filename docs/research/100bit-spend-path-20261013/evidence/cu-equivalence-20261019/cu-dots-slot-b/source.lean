import AspisR1CuDots.Funs

/-! Continuation form of the common complete emitted slot computation.
Both source callbacks are checked equal to this factorization, rather than
assuming that their final capture values can be erased. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.CuSavingsDotsSlot
open Aeneas Aeneas.Std Result AspisR1CuDots
open CuSavingsArrayBuilder
variable [Arithmetic]

def run {A : Type} (s : Slice U8) (a : Array field.wide_exact.WideExact 29#usize)
    (slot : Usize) (k : field.wide_exact.WideExact → Result A) : Result A := do
  let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    {start := 0#usize,«end» := 26#usize} 4#usize
  let limbs1 ←
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      iter s a slot (Array.repeat 8#usize 0#u64)
  let a1 ← core.array.from_fn 8#usize
    old_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 limbs1
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
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
      {start := 0#usize,«end» := 2#usize} s a slot tail1
  let we1 ← fast_pairing.EbyKDot.finish tail2
  let we2 ← field.wide_exact.WideExact.add value we1
  k we2

theorem old_factor (s : Slice U8) (a : Array field.wide_exact.WideExact 29#usize)
    (slot : Usize) :
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (s,a) slot = run s a slot (fun value => .ok (value,(s,a))) := by
  rfl

theorem new_factor (s : Array U8 608#usize)
    (a : Array field.wide_exact.WideExact 29#usize) (slot : Usize) :
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (s,a) slot = run s.to_slice a slot (fun value => .ok (value,(s,a))) := by
  rfl

private theorem remap_bind {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) :
    remap f (r >>= k) = (do let x ← r;remap f (k x)) := by
  cases r <;> rfl

private theorem remap_pair {A B C D : Type} (f : C → D) (pair : A × B)
    (k : A → B → Result C) :
    remap f (let (a,b) := pair;k a b) =
      (let (a,b) := pair;remap f (k a b)) := by
  cases pair;rfl

theorem naturality {A B : Type} (f : A → B) (s : Slice U8)
    (a : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (k : field.wide_exact.WideExact → Result A) :
    remap f (run s a slot k) = run s a slot (fun value => remap f (k value)) := by
  unfold run
  repeat first | rw [remap_bind] | rw [remap_pair]
  rfl

#print axioms old_factor
#print axioms new_factor
#print axioms naturality
end AspisR1.CuSavingsDotsSlot
