import CuSavingsRetainedDotsTail
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedDotsSuffix
open Aeneas Aeneas.Std Result AspisR1RetainedDots
open CuSavingsRetainedDotsBinding CuSavingsRetainedDotsTail
attribute [local irreducible] newPush oldPush newFinish oldFinish newDot oldDot
variable [AspisR1CanonicalDots.Shared]

def raw (common : Shared) (q : Slice U8) (g : G) (slot : Usize)
    (a1 : CuSavingsRetainedCompositionDelayedArrays.Canon) : Result (E × (Slice U8 × G)) :=
  letI : Shared := common
  do
  let o ← common.fromLimbs a1
  let value ← core.option.Option.unwrap o
  let tail ← common.newDot
  let we ← Array.index_usize g 28#usize
  let i ← slot * 120#usize
  let i1 ← i + 104#usize
  let i2 ← i + 120#usize
  let s1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) q {start:=i1,«end»:=i2}
  let o1 ← field.QM31.from_le_bytes s1
  let scalar ← core.option.Option.unwrap o1
  let (r,tail1) ← common.push tail we scalar
  core.result.Result.unwrap core.fmt.DebugUnit r
  let tail2 ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
    {start:=0#usize,«end»:=2#usize} q g slot tail1
  let out ← common.finish tail2
  let result ← common.add value out
  .ok (result,(q,g))

theorem source_factor (common : Shared) (q : Slice U8) (g : G) (slot : Usize)
    (a1 : CuSavingsRetainedCompositionDelayedArrays.Canon) :
    @CuSavingsRetainedCompositionDelayedKernel.suffix common (q,g) slot a1=raw common q g slot a1 := rfl

theorem source_eq (common : Shared) (q : Slice U8) (g : G) (hg : CanonicalG g)
    (slot : Usize) (limbs : CuSavingsRetainedCompositionDelayedArrays.Canon) :
    @CuSavingsRetainedCompositionDelayedKernel.suffix (newShared common) (q,g) slot limbs =
      @CuSavingsRetainedCompositionDelayedKernel.suffix (oldShared common) (q,g) slot limbs := by
  change raw (newShared common) q g slot limbs=raw (oldShared common) q g slot limbs
  unfold raw
  apply (bind_eq_iff _ _ _).mpr
  intro option _
  apply (bind_eq_iff _ _ _).mpr
  intro first _
  change (do
      let tail ← newDot
      let value ← Array.index_usize g 28#usize
      let i ← slot * 120#usize
      let i1 ← i + 104#usize
      let i2 ← i + 120#usize
      let bytes ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) q {start:=i1,«end»:=i2}
      let option ← @field.QM31.from_le_bytes (newShared common) bytes
      let scalar ← core.option.Option.unwrap option
      let (result,tail1) ← newPush tail value scalar
      core.result.Result.unwrap core.fmt.DebugUnit result
      let tail2 ← @old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
        (newShared common) {start:=0#usize,«end»:=2#usize} q g slot tail1
      let out ← newFinish tail2
      let combined ← common.add first out
      .ok (combined,(q,g))) = (do
      let tail ← oldDot
      let value ← Array.index_usize g 28#usize
      let i ← slot * 120#usize
      let i1 ← i + 104#usize
      let i2 ← i + 120#usize
      let bytes ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) q {start:=i1,«end»:=i2}
      let option ← @field.QM31.from_le_bytes (oldShared common) bytes
      let scalar ← core.option.Option.unwrap option
      let (result,tail1) ← oldPush tail value scalar
      core.result.Result.unwrap core.fmt.DebugUnit result
      let tail2 ← @old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
        (oldShared common) {start:=0#usize,«end»:=2#usize} q g slot tail1
      let out ← oldFinish tail2
      let combined ← common.add first out
      .ok (combined,(q,g)))
  rw [initializer]
  apply (bind_eq_iff _ _ _).mpr
  intro state _
  apply (bind_eq_iff _ _ _).mpr
  intro value hread
  have hc := hg _ value hread
  apply (bind_eq_iff _ _ _).mpr
  intro i0 _
  apply (bind_eq_iff _ _ _).mpr
  intro i1 _
  apply (bind_eq_iff _ _ _).mpr
  intro i2 _
  apply (bind_eq_iff _ _ _).mpr
  intro bytes _
  apply (bind_eq_iff _ _ _).mpr
  intro option _
  apply (bind_eq_iff _ _ _).mpr
  intro scalar _
  rw [push_equivalence state value scalar hc]
  apply (bind_eq_iff _ _ _).mpr
  intro pushed _
  rcases pushed with ⟨result,after⟩
  simp only [uncurry_apply_pair]
  apply (bind_eq_iff _ _ _).mpr
  intro unit _
  rw [CuSavingsRetainedDotsTail.loop_eq common q g hg slot]
  apply (bind_eq_iff _ _ _).mpr
  intro finalState _
  rw [finalizer]

#print axioms source_eq
end AspisR1.CuSavingsRetainedDotsSuffix
