import CuSavingsCanonicalVectorLoop
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace AspisR1.CuSavingsCanonicalTailStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalDotsField CuSavingsCanonicalVectorLoop
variable [Shared] [VectorCommon]

def input (q : Slice U8) (g : G) (slot term : Usize) :
    Result (field.wide_exact.WideExact × field.QM31) := do
  let i ← slot*32#usize
  let i1 ← 480#usize+i
  let i2 ← term*16#usize
  let offset ← i1+i2
  let i3 ← term+26#usize
  let value ← Array.index_usize g i3
  let i4 ← offset+16#usize
  let slice ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    q {start:=offset,«end»:=i4}
  let parsed ← field.QM31.from_le_bytes slice
  let scalar ← core.option.Option.unwrap parsed
  .ok (value,scalar)

def oldAdvance (state : old_pairing.EbyKDot) (value : field.wide_exact.WideExact)
    (scalar : field.QM31) : Result old_pairing.EbyKDot := do
  let (result,after) ← old_pairing.EbyKDot.push state value scalar
  core.result.Result.unwrap core.fmt.DebugUnit result
  .ok after

def newAdvance (state : new_pairing.EbyKDot) (value : field.wide_exact.WideExact)
    (scalar : field.QM31) : Result new_pairing.EbyKDot := do
  let (result,after) ← new_pairing.EbyKDot.push state value scalar
  core.result.Result.unwrap core.fmt.DebugUnit result
  .ok after

theorem advance_eq (state : old_pairing.EbyKDot) (value : field.wide_exact.WideExact)
    (scalar : field.QM31) (hv : WideCanonical value) (hc : RelatedCounts state) :
    newAdvance (project state) value scalar =
      (do let after ← oldAdvance state value scalar;.ok (project after)) := by
  unfold newAdvance oldAdvance
  rw [public_push state value scalar hv hc]
  simp only [bind_assoc_eq,bind_tc_ok]
  cases hp : old_pairing.EbyKDot.push state value scalar with
  | fail e => rfl
  | div => rfl
  | ok pair =>
      rcases pair with ⟨result,after⟩
      cases hu : core.result.Result.unwrap core.fmt.DebugUnit result <;>
        simp only [projectResult,bind_tc_ok,hu,bind_tc_fail,bind_tc_div]

private theorem bind_ok {A B : Type} (r : Result A) (k : A→Result B) (out : B)
    (h : (r >>=k)=.ok out) : ∃ value,r=.ok value ∧ k value=.ok out := by
  cases r with
  | fail e => cases h
  | div => cases h
  | ok value => exact ⟨value,rfl,h⟩

theorem advance_counts (state after : old_pairing.EbyKDot) (value : field.wide_exact.WideExact)
    (scalar : field.QM31) (hv : WideCanonical value) (hc : RelatedCounts state)
    (h : oldAdvance state value scalar=.ok after) : RelatedCounts after := by
  unfold oldAdvance at h
  obtain ⟨pair,hpush,h⟩ := bind_ok _ _ _ h
  rcases pair with ⟨result,out⟩
  simp only [uncurry_apply_pair] at h
  cases result with
  | Err error => cases h
  | Ok unit =>
      have heq : out=after := Result.ok.inj h
      cases heq
      exact CuSavingsCanonicalDotsInvariant.push_counts state after value scalar hv hc hpush

theorem read_canonical (g : G) (hg : CanonicalG g) (i : Usize)
    (value : field.wide_exact.WideExact) (h : Array.index_usize g i=.ok value) : WideCanonical value := by
  by_cases hi : i.val<g.val.length
  · rw [g_read g i hi] at h
    cases Result.ok.inj h
    exact hg i.val hi
  · unfold Array.index_usize at h
    simp only [Array.getElem?_Usize_eq,List.getElem?_eq_none (by omega)] at h
    cases h

theorem input_canonical (q : Slice U8) (g : G) (hg : CanonicalG g)
    (slot term : Usize) (value : field.wide_exact.WideExact) (scalar : field.QM31)
    (h : input q g slot term=.ok (value,scalar)) : WideCanonical value := by
  unfold input at h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨index,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨decoded,hr,h⟩ := bind_ok _ _ _ h
  have hv := read_canonical g hg index decoded hr
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  have heq := congrArg Prod.fst (Result.ok.inj h)
  cases heq
  exact hv

#print axioms advance_eq
#print axioms advance_counts
#print axioms read_canonical
#print axioms input_canonical
end AspisR1.CuSavingsCanonicalTailStep
