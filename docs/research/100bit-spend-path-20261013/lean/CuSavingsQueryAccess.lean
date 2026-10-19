import CuSavingsQueryConstants

/-! Successful execution of the actual query accessor implies a full-width
slice, even without a parser/index precondition. Failed checked operations
remain failures; they are not silently assumed to succeed. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsQueryAccess
open Aeneas Aeneas.Std Result AspisR1CuQuery
open CuSavingsQueryConstants

def width (v : transport.Variant) : Usize :=
  match v with
  | .S1 => 3360#usize
  | .S2 | .D => 4864#usize

def byWidth (bytes : Slice U8) (i w : Usize) : Result (Slice U8) := do
  let start ← i*w
  let next ← i+1#usize
  let stop ← next*w
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    bytes {start := start,«end» := stop}

theorem query_eq (view : verifier.View) (i : Usize) :
    verifier.View.query view i = byWidth view.query_bytes i (width view.variant) := by
  have h12 : (1#usize) ≠ 2#usize := by scalar_tac
  cases hv : view.variant <;>
    simp only [verifier.View.query,hv,folds_success,folds,bind_tc_ok,
      if_neg h12,ite_true,initial_size,second_size,
      add_eq 3360#usize 1504#usize 4864#usize (by scalar_tac),
      add_eq 3360#usize 0#usize 3360#usize (by scalar_tac),byWidth,width]

theorem bind_ok {A B : Type} (p : Result A) (k : A → Result B) (y : B)
    (h : (p >>= k) = .ok y) : ∃ x, p = .ok x ∧ k x = .ok y := by
  cases hp : p with
  | fail e => simp only [hp,bind_tc_fail] at h;cases h
  | div => simp only [hp,bind_tc_div] at h;cases h
  | ok x => exact ⟨x,rfl,by simpa only [hp,bind_tc_ok] using h⟩

theorem byWidth_length (bytes : Slice U8) (i w : Usize) (out : Slice U8)
    (h : byWidth bytes i w = .ok out) : out.val.length = w.val := by
  unfold byWidth at h
  obtain ⟨start,hs,h⟩ := bind_ok _ _ _ h
  obtain ⟨next,hn,h⟩ := bind_ok _ _ _ h
  obtain ⟨stop,he,h⟩ := bind_ok _ _ _ h
  have hstart := UScalar.mul_equiv i w
  change UScalar.mul i w = .ok start at hs
  rw [hs] at hstart
  have hnext := UScalar.add_equiv i 1#usize
  rw [hn] at hnext
  have hstop := UScalar.mul_equiv next w
  change UScalar.mul next w = .ok stop at he
  rw [he] at hstop
  have hone : (1#usize).val = 1 := by scalar_tac
  have hnval : next.val = i.val+1 := by simpa only [hone] using hnext.2.1
  have span : stop.val-start.val = w.val := by
    rw [hstop.2.1,hnval,Nat.add_mul,Nat.one_mul,hstart.2.1]
    omega
  simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice.index] at h
  split at h
  · rename_i hb
    have hout := congrArg Subtype.val (Result.ok.inj h).symm
    change out.val = bytes.val.slice start.val stop.val at hout
    rw [hout,List.slice_length,span]
    change start.val ≤ stop.val ∧ stop.val ≤ bytes.val.length at hb
    exact Nat.min_eq_right (by omega)
  · cases h

theorem query_length (view : verifier.View) (i : Usize) (out : Slice U8)
    (h : verifier.View.query view i = .ok out) :
    out.val.length = (width view.variant).val := by
  rw [query_eq] at h
  exact byWidth_length _ _ _ _ h

theorem query_prefix_bound (view : verifier.View) (i : Usize) (out : Slice U8)
    (h : verifier.View.query view i = .ok out) : 608 ≤ out.val.length := by
  rw [query_length view i out h]
  cases view.variant <;> simp only [width] <;> scalar_tac

#print axioms query_eq
#print axioms bind_ok
#print axioms byWidth_length
#print axioms query_length
#print axioms query_prefix_bound
end AspisR1.CuSavingsQueryAccess
