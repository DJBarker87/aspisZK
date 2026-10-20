import M31InverseFieldModel

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1M31Inverse.SquareProof
open R17CurrentM31Semantics

theorem canonical_decode_zero_iff (x : U32) (hc : x.val < P) :
    decode x = 0 ↔ x = 0#u32 := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    change (x.val : ZMod P).val = 0 at hv
    rw [ZMod.val_natCast_of_lt hc] at hv
    apply UScalar.eq_of_val_eq
    exact hv
  · intro h
    subst x
    rfl

theorem canonical_word_nonzero_iff (x : U32) (hc : x.val < P) :
    x ≠ 0#u32 ↔ decode x ≠ 0 := by
  exact not_congr (canonical_decode_zero_iff x hc).symm

theorem current_inv_success_inverse (x z : U32) (hx : decode x ≠ 0)
    (h : field.M31.inv AspisR1Qm31ArithmeticProbe.field.M31.mul x = .ok z) :
    decode z = (decode x)⁻¹ := by
  obtain ⟨z1,hz1,hv⟩ := current_inv_total_inverse x hx
  have he : z1 = z := Result.ok.inj (hz1.symm.trans h)
  subst z
  exact hv

theorem canonical_nonzero_inv_total (x : U32) (hc : x.val < P)
    (hx : x ≠ 0#u32) :
    ∃ z, field.M31.inv AspisR1Qm31ArithmeticProbe.field.M31.mul x = .ok z ∧
      decode z = (decode x)⁻¹ ∧ z.val < P := by
  obtain ⟨z,hz,hv⟩ := current_inv_total_inverse x ((canonical_word_nonzero_iff x hc).mp hx)
  exact ⟨z,hz,hv,current_inv_success_canonical x z hz⟩

#print axioms canonical_decode_zero_iff
#print axioms canonical_word_nonzero_iff
#print axioms current_inv_success_inverse
#print axioms canonical_nonzero_inv_total
end AspisR1M31Inverse.SquareProof
