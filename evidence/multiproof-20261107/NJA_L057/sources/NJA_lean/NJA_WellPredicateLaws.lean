import NJA_WellPredicates

set_option autoImplicit false
namespace NJA_WellPredicateLaws
open Aeneas Aeneas.Std Result NJA_Multiproof

theorem domain (x : U32) (c : multiproof.well_formed.closure_1) :
    multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut c x =
      ok (decide (x.val < 262144),c) := by
  unfold multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut
    multiproof.LEAF_BITS
  have word : U32.wrapping_shl 1#u32 18#u32 = 262144#u32 := by
    apply UScalar.eq_of_val_eq
    unfold U32.wrapping_shl UScalar.wrapping_shl
    change (1 <<< (18 % 32)) % 2^32 = 262144
    norm_num [Nat.one_shiftLeft]
  simp only [word,lift,bind_tc_ok]
  rfl

theorem slice_read (s : Slice U32) (i : Usize) (hi : i.val < s.val.length) :
    Slice.index_usize s i = ok (s.val[i.val]'hi) := by
  unfold Slice.index_usize
  change (match s.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (s.val[i.val]'hi)
  rw [List.getElem?_eq_getElem hi]

def pair (a b : U32) : Slice U32 := ⟨[a,b],by simp;scalar_tac⟩

theorem order (a b : U32) (c : multiproof.well_formed.closure) :
    multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool.call_mut c (pair a b) =
      ok (decide (a.val < b.val),c) := by
  unfold multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool.call_mut
  rw [slice_read (pair a b) 0#usize (by simp [pair]),
    slice_read (pair a b) 1#usize (by simp [pair])]
  rfl

#print axioms domain
#print axioms slice_read
#print axioms order
end NJA_WellPredicateLaws
