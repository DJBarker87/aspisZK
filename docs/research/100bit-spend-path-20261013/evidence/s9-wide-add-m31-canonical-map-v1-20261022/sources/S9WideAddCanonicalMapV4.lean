import AspisR1S9WideAddSourceBodyV1.Funs
import CurrentWideLinearExact

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideAddCanonicalMapV4

private abbrev P : Nat := AspisR1.ExtractedCurrentM31AddSub.P

private theorem source_m31_add_mod
    (x y : Std.U32) (hx : x.val < P) (hy : y.val < P) :
    ∃ z : Std.U32,
      AspisR1S9WideAddSourceBodyV1.field.M31.add x y = .ok z ∧
      z.val = (x.val + y.val) % P ∧ z.val < P := by
  have hP : P = 2147483647 := rfl
  have hsum : x.val + y.val < 2 ^ 32 := by
    rw [hP] at hx hy
    omega
  let s := Std.U32.wrapping_add x y
  have hs : s.val = x.val + y.val := by
    dsimp only [s]
    rw [Std.U32.wrapping_add_val_eq]
    simp only [UScalar.size, UScalarTy.numBits]
    exact Nat.mod_eq_of_lt hsum
  have hpv : AspisR1S9WideAddSourceBodyV1.field.P.val = P := by
    simp [P, AspisR1S9WideAddSourceBodyV1.field.P,
      AspisR1.ExtractedCurrentM31AddSub.P]
  have h2p : s.val < 2 * P := by rw [hs]; omega
  by_cases h : P ≤ s.val
  · have hsub : (Std.U32.wrapping_sub s AspisR1S9WideAddSourceBodyV1.field.P).val = s.val - P := by
      rw [Std.U32.wrapping_sub_val_eq, UScalar.size_UScalarTyU32, hpv]
      have harg : s.val + (Std.U32.size - P) = Std.U32.size + (s.val - P) := by
        simp [Std.U32.size, Std.U32.numBits, hP]
        omega
      rw [harg]
      have hlt : s.val - P < Std.U32.size := by
        simp [Std.U32.size, Std.U32.numBits, hP]
        omega
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt hlt]
    let z := Std.U32.wrapping_sub s AspisR1S9WideAddSourceBodyV1.field.P
    have hz : z.val = s.val - P := by simpa only [z] using hsub
    have hbody : AspisR1S9WideAddSourceBodyV1.field.M31.add x y = .ok z := by
      simp only [AspisR1S9WideAddSourceBodyV1.field.M31.add,
        lift, bind_tc_ok,
        UScalar.le_equiv]
      rw [hpv, if_pos h]
    refine ⟨z, hbody, ?_, ?_⟩
    · rw [hz, hs]
      have hsmall : x.val + y.val - P < P := by omega
      have hsumP : P ≤ x.val + y.val := by simpa only [hs] using h
      rw [Nat.mod_eq_sub_mod hsumP, Nat.mod_eq_of_lt hsmall]
    · rw [hz, hs]
      omega
  · have hsmall : s.val < P := Nat.lt_of_not_ge h
    let z := s
    have hz : z.val = s.val := rfl
    have hbody : AspisR1S9WideAddSourceBodyV1.field.M31.add x y = .ok z := by
      simp only [AspisR1S9WideAddSourceBodyV1.field.M31.add,
        lift, bind_tc_ok,
        UScalar.le_equiv]
      rw [hpv, if_neg (Nat.not_le_of_gt hsmall)]
    refine ⟨z, hbody, ?_, ?_⟩
    · have hsumlt : x.val + y.val < P := by rw [← hs]; exact hsmall
      rw [hz, hs]
      exact (Nat.mod_eq_of_lt hsumlt).symm
    · rw [hz]
      exact hsmall

theorem source_m31_add_maps_to_current
    (x y : Std.U32) (hx : x.val < P) (hy : y.val < P) :
    ∃ z : Std.U32,
      AspisR1S9WideAddSourceBodyV1.field.M31.add x y = .ok z ∧
      AspisR1CurrentWide.field.M31.add x y = .ok z := by
  obtain ⟨zs, hs, hvs, _⟩ := source_m31_add_mod x y hx hy
  obtain ⟨zc, hc, hvc, _⟩ :=
    AspisR1.ExtractedCurrentM31AddSub.current_add_mod x y hx hy
  have hcCurrent : AspisR1CurrentWide.field.M31.add x y = .ok zc := by
    rw [AspisR1CurrentWide.Proof.m31_add_same]
    exact hc
  have hv : zs.val = zc.val := by rw [hvs, hvc]
  have he : zs = zc := UScalar.eq_of_val_eq hv
  have hcSame : AspisR1CurrentWide.field.M31.add x y = .ok zs := by
    simpa only [← he] using hcCurrent
  exact ⟨zs, hs, hcSame⟩

#print axioms source_m31_add_mod
#print axioms source_m31_add_maps_to_current

end AspisR1S9WideAddCanonicalMapV4
