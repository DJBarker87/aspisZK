import R1Z.PV_RunJoin_CompactHigh39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactReject39
open Aeneas Aeneas.Std Result ProverRwFull

/-- The first nonzero high byte rejects before any low-byte append. This
retains the actual CodecError; it does not replace rejection with success. -/
theorem high (logical : Slice U8) (at1 bad : Usize) (value : U8)
    (bad_bound : bad.val<32) (nonzero : value≠0#u8)
    (read_bad : Slice.index_usize logical (Usize.wrapping_add at1 bad)=.ok value)
    (n : Nat) (first : Usize) (bound : first.val+n=bad.val)
    (before_bad : ∀ j : Usize, first.val≤j.val → j.val<bad.val →
      Slice.index_usize logical (Usize.wrapping_add at1 j)=.ok 0#u8) :
    host_compact.compact_values_loop0_loop0 logical at1 first =
      .ok (some (.Err compact.CodecError.NonZeroHigh)) := by
  induction n generalizing first with
  | zero =>
    have same : first=bad := UScalar.eq_of_val_eq (by omega)
    subst first
    unfold host_compact.compact_values_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_compact.compact_values_loop0_loop0.body,
      show bad<32#usize from bad_bound,↓reduceIte,lift,bind_tc_ok,read_bad,
      show (value != 0#u8)=true from (by simpa only [bne_iff_ne] using nonzero)]
  | succ n ih =>
    have hh : first.val<bad.val := by omega
    have inc : (Usize.wrapping_add first 1#usize).val=first.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      apply Nat.mod_eq_of_lt
      change first.val+1<UScalar.size .Usize
      have big := (32#usize).hSize
      change 32<UScalar.size .Usize at big
      omega
    have next := ih (Usize.wrapping_add first 1#usize) (by rw [inc];omega)
      (fun j hj hbad => before_bad j (by rw [inc] at hj;omega) hbad)
    unfold host_compact.compact_values_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_compact.compact_values_loop0_loop0.body,
      show first<32#usize from (by change first.val<32;omega),↓reduceIte,
      lift,bind_tc_ok,before_bad first (Nat.le_refl _) hh]
    exact next

#print axioms high
end R1Z.PV_RunJoin_CompactReject39
