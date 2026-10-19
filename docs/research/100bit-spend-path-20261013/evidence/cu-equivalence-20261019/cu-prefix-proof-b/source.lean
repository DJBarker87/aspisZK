import AspisR1CuPrefix.Funs

/-! Exact execution of the fixed-prefix statement, including its length
check, conversion, unwrap and short-input failure. Every admitted decoder
range reads the original bytes. View/query and four-dot caller composition
are separate source obligations. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsPrefix
open Aeneas Aeneas.Std Result

private theorem size_val : (608#usize).val = 608 := by scalar_tac

def prefixArray (q : Slice U8) (h : 608 ≤ q.val.length) : Array U8 608#usize :=
  ⟨q.val.take 608,by simp only [List.length_take,Nat.min_eq_left h,size_val]⟩

theorem source_success (q : Slice U8) (h : 608 ≤ q.val.length) :
    AspisR1CuPrefix.fixed_prefix q = .ok (prefixArray q h) := by
  let s := (prefixArray q h).to_slice
  have hl : s.val.length = 608 := by
    simpa only [size_val] using (prefixArray q h).property
  have hs : s.len = 608#usize := by
    apply UScalar.eq_of_val_eq
    simpa only [size_val,Slice.length] using (Slice.len_val s).trans hl
  have hq : (608#usize).val ≤ q.length := by
    simpa only [size_val,Slice.length] using h
  have hi : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      q {«end» := 608#usize} = .ok s := by
    simp only [core.slice.index.Slice.index,
      core.slice.index.SliceIndexRangeToUsizeSlice.index]
    rw [if_pos hq]
    simp only [List.slice_zero_j,size_val]
    rfl
  unfold AspisR1CuPrefix.fixed_prefix
  rw [hi]
  simp only [bind_tc_ok,core.array.TryFromSharedArraySlice.try_from,dif_pos hs]
  rfl

theorem source_short (q : Slice U8) (h : q.val.length < 608) :
    AspisR1CuPrefix.fixed_prefix q = .fail .panic := by
  have hq : ¬ (608#usize).val ≤ q.length := by
    simp only [size_val,Slice.length]
    omega
  simp only [AspisR1CuPrefix.fixed_prefix,core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]
  rw [if_neg hq]
  rfl

theorem read_eq (q : Slice U8) (h : 608 ≤ q.val.length) (i : Nat) (hi : i < 608) :
    (prefixArray q h).val[i]'(by rw [(prefixArray q h).property,size_val];exact hi) =
      q.val[i]'(by omega) := by
  simp only [prefixArray,List.getElem_take]

theorem range_eq (q : Slice U8) (h : 608 ≤ q.val.length) (start finish : Nat)
    (hf : finish ≤ 608) :
    (prefixArray q h).val.slice start finish = q.val.slice start finish := by
  simp only [prefixArray,List.slice,List.drop_take,List.take_take]
  rw [Nat.min_eq_left (show finish-start ≤ 608-start by omega)]

theorem base_range (slot term : Nat) (hs : slot < 4) (ht : term < 26) :
    slot*120+term*4 < slot*120+term*4+4 ∧ slot*120+term*4+4 ≤ 608 := by omega

theorem middle_range (slot : Nat) (hs : slot < 4) :
    slot*120+104 < slot*120+120 ∧ slot*120+120 ≤ 608 := by omega

theorem tail_range (slot term : Nat) (hs : slot < 4) (ht : term < 2) :
    480+slot*32+term*16 < 480+slot*32+term*16+16 ∧
      480+slot*32+term*16+16 ≤ 608 := by omega

#print axioms source_success
#print axioms source_short
#print axioms read_eq
#print axioms range_eq
#print axioms base_range
#print axioms middle_range
#print axioms tail_range
end AspisR1.CuSavingsPrefix
