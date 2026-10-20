import S3PairLowCallLowStepV1

open Aeneas Aeneas.Std Result WP
set_option autoImplicit false

namespace AspisR1PairLowCallCut

open AspisR1S3PowersLowEntryCanonicalV1

theorem actual_pair_callback_reads
    (c : weights.s2_twofold_low_array.closure)
    (i : Std.Usize) (hi : i.val < 16) :
    ∃ r d p q x y,
      UScalar.rem i (4#usize) = .ok r ∧
      UScalar.div i (4#usize) = .ok d ∧
      Array.index_usize weights.PERM r = .ok p ∧
      Array.index_usize weights.PERM d = .ok q ∧
      Array.index_usize c.1 p = .ok x ∧
      Array.index_usize c.2 q = .ok y ∧
      r.val = i.val % 4 ∧ d.val = i.val / 4 ∧
      p.val = lowPerm r.val ∧ q.val = lowPerm d.val ∧
      (closureToLowInputs c).1.getD (lowPerm (i.val % 4))
        AspisR1CurrentPowers.field.WideExact.ONE = generatedToPower x ∧
      (closureToLowInputs c).2.getD (lowPerm (i.val / 4))
        AspisR1CurrentPowers.field.WideExact.ONE = generatedToPower y := by
  have h4 : (4#usize).val = 4 := by decide
  have hden : (4#usize).val ≠ 0 := by omega
  obtain ⟨r0, hrem0, hremVal0⟩ :=
    WP.spec_imp_exists (UScalar.rem_spec i (y := 4#usize) hden)
  have hrem : UScalar.rem i (4#usize) = .ok r0 := by
    simpa [HMod.hMod] using hrem0
  have hremVal : r0.val = i.val % 4 := by simpa [h4] using hremVal0
  obtain ⟨d0, hdiv, hdivVal0⟩ :=
    @UScalar.div_spec .Usize i (4#usize) hden
  have hdivVal : d0.val = i.val / 4 := by simpa [h4] using hdivVal0
  have hrem_lt : r0.val < 4 := by rw [hremVal]; omega
  have hdiv_lt : d0.val < 4 := by rw [hdivVal]; omega
  obtain ⟨p0, hp0, hpval0⟩ := perm_read_ok r0 hrem_lt
  obtain ⟨q0, hq0, hqval0⟩ := perm_read_ok d0 hdiv_lt
  have hpbound : p0.val < c.1.val.length := by
    simpa [c.1.property, h4, hpval0] using lowPerm_lt4 r0.val
  have hqbound : q0.val < c.2.val.length := by
    simpa [c.2.property, h4, hqval0] using lowPerm_lt4 d0.val
  obtain ⟨x0, hx0, hxval0⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec c.1 p0 hpbound)
  obtain ⟨y0, hy0, hyval0⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec c.2 q0 hqbound)
  have hleft : (closureToLowInputs c).1.getD (lowPerm (i.val % 4))
      AspisR1CurrentPowers.field.WideExact.ONE = generatedToPower x0 := by
    calc
      _ = generatedToPower (c.1.val[lowPerm (i.val % 4)]'(
          by simpa [c.1.property, h4] using lowPerm_lt4 (i.val % 4))) :=
        closure_left_getD c (lowPerm (i.val % 4)) (lowPerm_lt4 (i.val % 4))
      _ = generatedToPower x0 := by
        congr 1
        have hpval : p0.val = lowPerm (i.val % 4) := by
          simpa [hremVal] using hpval0
        simpa [hpval] using hxval0.symm
  have hright : (closureToLowInputs c).2.getD (lowPerm (i.val / 4))
      AspisR1CurrentPowers.field.WideExact.ONE = generatedToPower y0 := by
    calc
      _ = generatedToPower (c.2.val[lowPerm (i.val / 4)]'(
          by simpa [c.2.property, h4] using lowPerm_lt4 (i.val / 4))):=
        closure_right_getD c (lowPerm (i.val / 4)) (lowPerm_lt4 (i.val / 4))
      _ = generatedToPower y0 := by
        congr 1
        have hqval : q0.val = lowPerm (i.val / 4) := by
          simpa [hdivVal] using hqval0
        simpa [hqval] using hyval0.symm
  exact ⟨r0, d0, p0, q0, x0, y0, hrem, hdiv, hp0, hq0, hx0, hy0,
    hremVal, hdivVal, hpval0, hqval0, hleft, hright⟩

#print axioms actual_pair_callback_reads

end AspisR1PairLowCallCut
