import S3PairLowCallOpsAdapterV1

open Aeneas Aeneas.Std Result WP
set_option autoImplicit false

namespace AspisR1PairLowCallCut

open AspisR1S3PowersLowEntryCanonicalV1

def closureToLowInputs (c : weights.s2_twofold_low_array.closure) : LowInputs :=
  (c.1.val.map generatedToPower, c.2.val.map generatedToPower)

theorem toActualS_generatedToPower_eq_powerToS (x : field.WideExact) :
    toActualS x = AspisR1S3PowersLowEntryCanonicalV1.powerToS
      (generatedToPower x) := by
  cases x <;> rfl

private theorem lowPerm_eq_perm_value_nat (n : Nat) (hn : n < 4) :
    lowPerm n = (weights.PERM.val[n]'(by
      have hlen := Array.length_eq weights.PERM
      have hn4 : (4#usize).val = 4 := by decide
      omega)).val := by
  interval_cases n <;> norm_num [lowPerm, weights.PERM, Array.make]

theorem lowPerm_eq_perm_value (i : Std.Usize) (hi : i.val < 4) :
    lowPerm i.val = (weights.PERM.val[i.val]'(by
      have hlen := Array.length_eq weights.PERM
      have hn4 : (4#usize).val = 4 := by decide
      omega)).val := lowPerm_eq_perm_value_nat i.val hi

theorem perm_read_ok (i : Std.Usize) (hi : i.val < 4) :
    ∃ j, Array.index_usize weights.PERM i = .ok j ∧
      j.val = lowPerm i.val := by
  have hlen := Array.length_eq weights.PERM
  have hn4 : (4#usize).val = 4 := by decide
  have hbound : i.val < weights.PERM.val.length := by omega
  obtain ⟨j, hread, hvalue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec weights.PERM i hbound)
  refine ⟨j, hread, ?_⟩
  rw [hvalue]
  exact (lowPerm_eq_perm_value i hi).symm

end AspisR1PairLowCallCut
