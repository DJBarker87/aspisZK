import V7CallerCurrentReleaseR26FieldBridge

/-!
# Successful fixed-field reads are canonical

The generated fixed-field reader rejects each of the four M31 limbs when it
is greater than or equal to the source modulus.  This module records the
canonicality consequence of one successful literal reader call.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30FixedFieldCanonical

open V7CallerCurrentReleaseR26FieldBridge

theorem fixed_reader_next_qm31_canonical
    (reader next : v6_onefold.V6FixedFieldReader)
    (value : field.QM31)
    (success :
      v6_onefold.V6FixedFieldReader.impl.next_qm31 reader =
        ok (.Ok value, next)) :
    GeneratedCanonicalQM31 value := by
  unfold v6_onefold.V6FixedFieldReader.impl.next_qm31 at success
  by_cases remainingZero : reader.remaining = 0#usize
  · simp [remainingZero] at success
  · simp [remainingZero] at success
    cases read : v6_onefold.PackedM31Reader.impl.qm31 reader.packed <;>
      simp [read] at success
    rename_i pair
    rcases pair with ⟨raw, packedNext⟩
    by_cases h00 : field.P.val ≤ raw.c0.a.val
    · simp [h00, Std.lift, bind_tc_ok] at success
    · simp [h00, Std.lift, bind_tc_ok] at success
      by_cases h01 : field.P.val ≤ raw.c0.b.val
      · simp [h01] at success
      · simp [h01] at success
        by_cases h10 : field.P.val ≤ raw.c1.a.val
        · simp [h10] at success
        · simp [h10] at success
          by_cases h11 : field.P.val ≤ raw.c1.b.val
          · simp [h11] at success
          · simp [h11] at success
            rcases success with ⟨rfl, rfl⟩
            unfold GeneratedCanonicalQM31 GeneratedCanonicalCM31
              AspisAeneasCM31Multiplicative.CanonicalRawM31
              AspisAeneasCM31Multiplicative.m31Modulus
            have h00' : raw.c0.a.val < field.P.val := Nat.lt_of_not_ge h00
            have h01' : raw.c0.b.val < field.P.val := Nat.lt_of_not_ge h01
            have h10' : raw.c1.a.val < field.P.val := Nat.lt_of_not_ge h10
            have h11' : raw.c1.b.val < field.P.val := Nat.lt_of_not_ge h11
            simpa [field.P] using
              And.intro (And.intro h00' h01') (And.intro h10' h11')

#print axioms fixed_reader_next_qm31_canonical

end V7CallerCurrentReleaseR30FixedFieldCanonical
