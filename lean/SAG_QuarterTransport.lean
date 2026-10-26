import R1RoundPairing
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_QuarterTransport

theorem value {K L : Type} [Field K] [Field L] (f : K →+* L) (q : K)
    (base : (4 : K) * q = 1) : f q = (4 : L)⁻¹ := by
  have four_times : (4 : L) * f q = 1 := by
    have lifted := congrArg f base
    simpa only [map_mul,map_ofNat,map_one] using lifted
  have nz : (4 : L) ≠ 0 := by
    intro h
    rw [h,zero_mul] at four_times
    exact zero_ne_one four_times
  calc
    f q = (4 : L)⁻¹ * ((4 : L) * f q) := by
      rw [←mul_assoc,inv_mul_cancel₀ nz,one_mul]
    _ = (4 : L)⁻¹ := by rw [four_times,mul_one]

#print axioms value
end AspisR1.SAG_QuarterTransport
end
