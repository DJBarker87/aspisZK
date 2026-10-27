import SAQ_InverseSourceModel
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1M31Inverse.SquareProof
open R17CurrentM31Semantics

theorem current_inv_total_inverse (x : U32) (hx : decode x ≠ 0) :
    ∃ z, field.M31.inv AspisR1Qm31ArithmeticProbe.field.M31.mul x = .ok z ∧
      decode z = (decode x)⁻¹ := by
  have hrawne : x ≠ 0#u32 := by
    intro he
    apply hx
    subst x
    rfl
  have hraw : x != 0#u32 := by simpa only [bne_iff_ne] using hrawne
  obtain ⟨z,hz,hpow⟩ := current_inv_total_power x hraw
  refine ⟨z,hz,?_⟩
  have hfermat : decode x ^ 2147483646 = 1 := ZMod.pow_card_sub_one_eq_one hx
  have hmul : decode x * decode z = 1 := by
    rw [hpow,mul_comm,← pow_succ]
    exact hfermat
  exact eq_inv_of_mul_eq_one_right hmul

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem current_inv_success_canonical (x z : U32)
    (h : field.M31.inv AspisR1Qm31ArithmeticProbe.field.M31.mul x = .ok z) :
    z.val < 2147483647 := by
  unfold field.M31.inv at h
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨_,_,h⟩
  rcases bind_ok_inv h with ⟨a,_,h⟩
  obtain ⟨out,ho,_,hc⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod a x
  have he : out = z := Result.ok.inj (ho.symm.trans h)
  subst z
  exact hc

#print axioms current_inv_total_inverse
#print axioms current_inv_success_canonical
end AspisR1M31Inverse.SquareProof
