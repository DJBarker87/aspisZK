import R1M31ParserRefinement

/-! Consequences of the focused extracted-parser refinement: acceptance and
rejection are exactly the retained modulus test, and successful values are
canonical with the retained little-endian word value. -/
set_option autoImplicit false

namespace AspisR1.M31ParserCanonicality

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec
open AspisR1.M31ParserRefinement

def accepted (bytes : WordBytes) : Prop :=
  ∃ value : U32,
    AspisR1M31Parser.field.M31.from_le_bytes (wordArray bytes) =
      Result.ok (some value)

def rejected (bytes : WordBytes) : Prop :=
  AspisR1M31Parser.field.M31.from_le_bytes (wordArray bytes) =
    Result.ok none

theorem accepted_iff (bytes : WordBytes) :
    accepted bytes ↔
      (decodeWordLE bytes).val < m31Modulus := by
  unfold accepted
  rw [from_le_bytes_refines]
  unfold decodeM31LE
  by_cases h : (decodeWordLE bytes).val < m31Modulus
  · simp [h]
  · simp [h]

theorem rejected_iff (bytes : WordBytes) :
    rejected bytes ↔
      m31Modulus ≤ (decodeWordLE bytes).val := by
  unfold rejected
  rw [from_le_bytes_refines]
  unfold decodeM31LE
  by_cases h : (decodeWordLE bytes).val < m31Modulus
  · simp [h]
  · simp [h]

theorem successful_value_canonical (bytes : WordBytes) (value : U32)
    (hparsed :
      AspisR1M31Parser.field.M31.from_le_bytes (wordArray bytes) =
        Result.ok (some value)) :
    value.val < m31Modulus ∧
      value.val = (decodeWordLE bytes).val := by
  rw [from_le_bytes_refines] at hparsed
  have hoption : Option.map valueToU32 (decodeM31LE bytes) = some value :=
    Result.ok.inj hparsed
  by_cases hcanonical : (decodeWordLE bytes).val < m31Modulus
  · let decoded : M31Value := ⟨(decodeWordLE bytes).val, hcanonical⟩
    have hdecoded : decodeM31LE bytes = some decoded := by
      simp [decodeM31LE, decoded, hcanonical]
    rw [hdecoded] at hoption
    have hvalue : valueToU32 decoded = value := Option.some.inj hoption
    constructor
    · rw [← hvalue, valueToU32_val]
      exact decoded.isLt
    · rw [← hvalue, valueToU32_val]
      rfl
  · simp [decodeM31LE, hcanonical] at hoption

#print axioms accepted_iff
#print axioms rejected_iff
#print axioms successful_value_canonical

end AspisR1.M31ParserCanonicality
