import S8Kani2MutableLoop
import S8Kani2SliceSet
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open S8Kani2MutableExtraction.batched_weights
namespace BwPrefixWriteIndex
abbrev FieldQM := AspisR1BatchedWeightsExtraction.aspis_core.field.QM31
variable (f : Nat → FieldQM)

theorem suffix_index_unchanged (n : Nat) (s : Slice FieldQM) (i : Usize)
    (hn : n ≤ s.len.val) (hi : n ≤ i.val) (hibound : i.val < s.len.val) :
    Slice.index_usize (prefixWrite f 0 n s) i = Slice.index_usize s i := by
  induction n generalizing s i with
  | zero => simp [prefixWrite]
  | succ n ih =>
      simp only [prefixWrite, Nat.zero_le, if_true]
      have hlen : (s.setAtNat n (f n)).len.val = s.len.val := by
        simp [Slice.len, Slice.setAtNat]
      have hn' : n ≤ (s.setAtNat n (f n)).len.val := by rw [hlen]; omega
      have hprefix := ih (s.setAtNat n (f n)) i hn' (Nat.le_trans (Nat.le_succ n) hi) (by rw [hlen]; exact hibound)
      have hidx : i.val < s.len.val := hibound
      have hset := BwSliceSetIndexLemmas.setAtNat_ne s i n (f n) hidx (by omega)
        (by omega : i.val ≠ n)
      exact hprefix.trans hset

theorem prefixWrite_index (n : Nat) (s : Slice FieldQM) (i : Usize)
    (hn : n ≤ s.len.val) (hi : i.val < n) :
    Slice.index_usize (prefixWrite f 0 n s) i = .ok (f i.val) := by
  induction n generalizing s i with
  | zero => omega
  | succ n ih =>
      simp only [prefixWrite, Nat.zero_le, if_true]
      have hlen : (s.setAtNat n (f n)).len.val = s.len.val := by
        simp [Slice.len, Slice.setAtNat]
      by_cases hlt : i.val < n
      · exact ih (s.setAtNat n (f n)) i (by rw [hlen]; omega) hlt
      · have heq : i.val = n := by omega
        have hprefix := suffix_index_unchanged f n (s.setAtNat n (f n)) i
          (by rw [hlen]; omega) (by omega) (by rw [hlen]; omega)
        have hset := BwSliceSetIndexLemmas.setAtNat_same s i n (f n) (by omega) heq
        simpa [heq] using hprefix.trans hset

#print axioms suffix_index_unchanged
#print axioms prefixWrite_index
end BwPrefixWriteIndex
