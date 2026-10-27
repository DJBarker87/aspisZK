import R1Z.PV_Src_ExternalSums

/-! Exact unreduced U64 column sums in the owned external layer. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalSumStep
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderPoseidonReference
abbrev State := Array U32 16#usize
abbrev Sums := Array U64 4#usize

def cell (s : State) (col : Usize) : U64 :=
  U64.wrapping_add (U64.wrapping_add (U64.wrapping_add
    (UScalar.cast .U64 s.val[col.val]!)
    (UScalar.cast .U64 s.val[col.val+4]!))
    (UScalar.cast .U64 s.val[col.val+8]!))
    (UScalar.cast .U64 s.val[col.val+12]!)

theorem offset (col : Usize) (hc : col.val < 4) (k : Usize) (hk : k.val ≤ 12) :
    (Usize.wrapping_add col k).val = col.val+k.val := by
  rw [uadd _ _ (by omega)]

theorem step (s : State) (sums : Sums) (col : Usize) (hc : col.val < 4) :
    poseidon2.builder_reference.external_owned_loop1 s sums col =
      poseidon2.builder_reference.external_owned_loop1 s (sums.set col (cell s col))
        (Usize.wrapping_add col 1#usize) := by
  rw [poseidon2.builder_reference.external_owned_loop1,
    if_pos (by simpa [UScalar.lt_equiv] using hc),index_ok s col (by simp;omega)]
  simp only [lift,bind_tc_ok]
  rw [index_ok s _ (by rw [offset col hc _ (by decide)];simp;omega)]
  simp only [lift,bind_tc_ok]
  rw [index_ok s _ (by rw [offset col hc _ (by decide)];simp;omega)]
  simp only [lift,bind_tc_ok]
  rw [index_ok s _ (by rw [offset col hc _ (by decide)];simp;omega)]
  simp only [lift,bind_tc_ok]
  rw [BuilderRecordsArray.update_gen _ col _ (by simpa using hc)]
  simp only [lift,bind_tc_ok,cell,offset col hc 4#usize (by decide),
    offset col hc 8#usize (by decide),offset col hc 12#usize (by decide),
    UScalar.ofNatCore_val_eq]

#print axioms offset
#print axioms step
end R1Z.PV_Src_ExternalSumStep
