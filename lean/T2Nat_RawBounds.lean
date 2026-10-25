import Port5Q2_ReaderRaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_RawBounds
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem range_success {T : Type} (s out : Slice T) (start finish : Usize)
    (actual : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice T)
      s ⟨start,finish⟩ = ok out) : start.val ≤ finish.val ∧ finish.val ≤ s.val.length := by
  rw [Slice.index_SliceIndexRangeUsizeSliceInst] at actual
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at actual
  split at actual
  · assumption
  · cases actual

theorem checked_success (N : Usize) (r : verifier.Reader)
    (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (out : Array U8 N × verifier.Reader)
    (actual : verifier.Reader.rawWithUnwrap N unwrap r = ok out) :
    r.at.val + N.val ≤ r.bytes.val.length := by
  unfold verifier.Reader.rawWithUnwrap at actual
  obtain ⟨finish,add,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨slice,index,_⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  have bound := range_success r.bytes slice r.at finish index
  have eq := UScalar.add_equiv r.at N
  rw [add] at eq
  have value : finish.val = r.at.val + N.val := eq.2.1
  omega

/-- A successful source range cannot straddle usize wraparound: the source
slice requires start ≤ wrapped end. No checkpoint content assumption. -/
theorem no_wrap (x y : Usize) (order : x.val ≤ (Usize.wrapping_add x y).val) :
    (Usize.wrapping_add x y).val = x.val+y.val := by
  rw [Usize.wrapping_add_val_eq] at order ⊢
  have hx : x.val < UScalar.size .Usize := by simpa only [UScalar.size] using x.hBounds
  have hy : y.val < UScalar.size .Usize := by simpa only [UScalar.size] using y.hBounds
  by_cases small : x.val+y.val < UScalar.size .Usize
  · exact Nat.mod_eq_of_lt small
  · have lower : UScalar.size .Usize ≤ x.val+y.val := by omega
    have rest : x.val+y.val-UScalar.size .Usize < UScalar.size .Usize := by omega
    have modulo : (x.val+y.val)%UScalar.size .Usize = x.val+y.val-UScalar.size .Usize := by
      conv_lhs => rw [← Nat.sub_add_cancel lower]
      rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt rest]
    rw [modulo] at order
    omega

theorem current_success (N : Usize) (r : verifier.Reader)
    (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (out : Array U8 N × verifier.Reader)
    (actual : Port5Q2_ReaderRaw.raw N unwrap r = ok out) :
    r.at.val + N.val ≤ r.bytes.val.length := by
  unfold Port5Q2_ReaderRaw.raw at actual
  simp only [lift,bind_tc_ok] at actual
  obtain ⟨slice,index,_⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  have bounds := range_success r.bytes slice r.at (Usize.wrapping_add r.at N) index
  rw [no_wrap r.at N bounds.1] at bounds
  exact bounds.2

#print axioms range_success
#print axioms checked_success
#print axioms no_wrap
#print axioms current_success
end AspisR1.T2Nat_RawBounds
end
