import AspisR1RhoParser.Funs
import CuSavingsRhoParserM31

set_option autoImplicit false

namespace AspisR1.CuSavingsRhoParserCanonicality

open Aeneas Aeneas.Std Result

abbrev M31 := AspisR1CuRho.field.M31
abbrev CM31 := AspisR1CuRho.field.CM31
abbrev QM31 := AspisR1CuRho.field.QM31
abbrev P := AspisR1CuRho.field.P

private theorem eliminate_success_none {α : Type} {x : α}
    (h : (Result.ok (none : Option α)) = Result.ok (some x)) : False := by
  cases h

theorem cm31_from_le_bytes_success_canonical
    (bytes : Slice U8) (x : CM31)
    (h : AspisR1CuRho.field.CM31.from_le_bytes bytes =
      Result.ok (some x)) :
    x.a.val < P.val ∧ x.b.val < P.val := by
  unfold AspisR1CuRho.field.CM31.from_le_bytes at h
  cases hs0 : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      { start := 0#usize, «end» := 4#usize } with
  | fail e => simp [hs0] at h
  | div => simp [hs0] at h
  | ok s0 =>
      simp only [hs0, bind_tc_ok] at h
      cases hc0 : core.array.TryFromArrayCopySlice.try_from
          4#usize core.marker.CopyU8 s0 with
      | fail e => simp [hc0] at h
      | div => simp [hc0] at h
      | ok r0 =>
          simp only [hc0, bind_tc_ok] at h
          cases r0 with
          | Err _ => simp at h
          | Ok v0 =>
              cases hm0 : AspisR1CuRho.field.M31.from_le_bytes v0 with
              | fail e => simp [hm0] at h
              | div => simp [hm0] at h
              | ok o0 =>
                  simp only [hm0, bind_tc_ok] at h
                  cases o0 with
                  | none =>
                      have hdisc : Aeneas.Std.read_discriminant
                          (none : Option Aeneas.Std.core.convert.Infallible) = 0#isize := rfl
                      simp [AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                        Aeneas.Std.massert, hdisc] at h
                  | some a0 =>
                      simp only [AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        bind_tc_ok] at h
                      cases hs1 : core.slice.index.Slice.index
                          (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
                          { start := 4#usize, «end» := 8#usize } with
                      | fail e => simp [hs1] at h
                      | div => simp [hs1] at h
                      | ok s1 =>
                          simp only [hs1, bind_tc_ok] at h
                          cases hc1 : core.array.TryFromArrayCopySlice.try_from
                              4#usize core.marker.CopyU8 s1 with
                          | fail e => simp [hc1] at h
                          | div => simp [hc1] at h
                          | ok r1 =>
                              simp only [hc1, bind_tc_ok] at h
                              cases r1 with
                              | Err _ => simp at h
                              | Ok v1 =>
                                  cases hm1 : AspisR1CuRho.field.M31.from_le_bytes v1 with
                                  | fail e => simp [hm1] at h
                                  | div => simp [hm1] at h
                                  | ok o1 =>
                                      simp only [hm1, bind_tc_ok] at h
                                      cases o1 with
                                      | none =>
                                          have hdisc : Aeneas.Std.read_discriminant
                                              (none : Option Aeneas.Std.core.convert.Infallible) = 0#isize := rfl
                                          simp [AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                                            AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                                            Aeneas.Std.massert, hdisc] at h
                                      | some b0 =>
                                          simp only [AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                                            bind_tc_ok, Result.ok.injEq,
                                            Option.some.injEq] at h
                                          cases h
                                          constructor
                                          · exact AspisR1.CuSavingsRhoParserM31.m31_from_le_bytes_success_canonical _ _ hm0
                                          · exact AspisR1.CuSavingsRhoParserM31.m31_from_le_bytes_success_canonical _ _ hm1

theorem qm31_from_le_bytes_success_canonical
    (bytes : Slice U8) (x : QM31)
    (h : AspisR1CuRho.field.QM31.from_le_bytes bytes =
      Result.ok (some x)) :
    x.c0.a.val < P.val ∧ x.c0.b.val < P.val ∧
      x.c1.a.val < P.val ∧ x.c1.b.val < P.val := by
  unfold AspisR1CuRho.field.QM31.from_le_bytes at h
  cases hs0 : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      { start := 0#usize, «end» := 8#usize } with
  | fail e => simp [hs0] at h
  | div => simp [hs0] at h
  | ok s0 =>
      simp only [hs0, bind_tc_ok] at h
      cases hc0 : AspisR1CuRho.field.CM31.from_le_bytes s0 with
      | fail e => simp [hc0] at h
      | div => simp [hc0] at h
      | ok o0 =>
          cases o0 with
          | none =>
              rw [hc0] at h
              simp only [bind_tc_ok] at h
              have hdisc : Aeneas.Std.read_discriminant
                  (none : Option Aeneas.Std.core.convert.Infallible) = 0#isize := rfl
              simp [AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                Aeneas.Std.massert, hdisc] at h
          | some a0 =>
              rw [hc0] at h
              simp only [bind_tc_ok] at h
              simp only [AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                bind_tc_ok] at h
              cases hs1 : core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
                  { start := 8#usize, «end» := 16#usize } with
              | fail e => simp [hs1] at h
              | div => simp [hs1] at h
              | ok s1 =>
                  simp only [hs1, bind_tc_ok] at h
                  cases hc1 : AspisR1CuRho.field.CM31.from_le_bytes s1 with
                  | fail e => simp [hc1] at h
                  | div => simp [hc1] at h
                  | ok o1 =>
                      cases o1 with
                      | none =>
                          rw [hc1] at h
                          simp only [bind_tc_ok] at h
                          have hdisc : Aeneas.Std.read_discriminant
                              (none : Option Aeneas.Std.core.convert.Infallible) = 0#isize := rfl
                          simp [AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                            AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                            Aeneas.Std.massert, hdisc] at h
                      | some a1 =>
                          rw [hc1] at h
                          simp only [bind_tc_ok] at h
                          simp only [AspisR1CuRho.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                            bind_tc_ok, Result.ok.injEq,
                            Option.some.injEq] at h
                          cases h
                          obtain ⟨h00, h01⟩ := cm31_from_le_bytes_success_canonical _ _ hc0
                          obtain ⟨h10, h11⟩ := cm31_from_le_bytes_success_canonical _ _ hc1
                          exact ⟨h00, h01, h10, h11⟩

#print axioms cm31_from_le_bytes_success_canonical
#print axioms qm31_from_le_bytes_success_canonical

end AspisR1.CuSavingsRhoParserCanonicality
