import AspisV8R19.R635DecoderWholeCanonical

set_option autoImplicit false

namespace AspisV8R19.R638CombineAcceptedInputs

open Aeneas Aeneas.Std Result ControlFlow
open Aeneas.Std.WP
open AspisR614SelectedCombineBeta
open AspisV8R19.R635DecoderWholeCanonical

/-- Successful actual `combine_beta` has accepted complete fixed-width decoded
inputs and an exact opaque loop result. -/
theorem combine_accepted_inputs (c1 c2 : Slice U8)
    (powers : query_arithmetic.BetaCoefficients)
    (z : Array aspis_core.field.QM31 4#usize)
    (h : query_arithmetic.combine_beta c1 c2 powers =
      .ok (core.result.Result.Ok z)) :
    ∃ a1 : Array U32 104#usize, ∃ a2 : Array U32 48#usize,
      query_arithmetic.r55_decode_into c1 (Array.repeat 104#usize 0#u32) =
        .ok (core.result.Result.Ok (), a1) ∧
      query_arithmetic.r55_decode_into c2 (Array.repeat 48#usize 0#u32) =
        .ok (core.result.Result.Ok (), a2) ∧
      (∀ value ∈ a1.val, value.val < 2147483647) ∧
      (∀ value ∈ a2.val, value.val < 2147483647) ∧
      query_arithmetic.combine_beta_loop { start := 0#usize, «end» := 4#usize }
        powers a1 a2 (Array.repeat 4#usize aspis_core.field.QM31.ZERO) = .ok z := by
  unfold query_arithmetic.combine_beta at h
  cases h1 : query_arithmetic.r55_decode_into c1 (Array.repeat 104#usize 0#u32) with
  | fail e => simp [h1, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame] at h
  | div => simp [h1, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame] at h
  | ok pair =>
    rcases pair with ⟨r, a1⟩
    cases r with
    | Err e => simp [h1, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame] at h
    | Ok u =>
      cases u
      simp [core.result.Result.Insts.CoreOpsTry.branch, h1] at h
      cases h2 : query_arithmetic.r55_decode_into c2 (Array.repeat 48#usize 0#u32) with
      | fail e => simp [h2, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame] at h
      | div => simp [h2, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame] at h
      | ok pair =>
        rcases pair with ⟨r2, a2⟩
        cases r2 with
        | Err e => simp [h2, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame] at h
        | Ok u2 =>
          cases u2
          simp [core.result.Result.Insts.CoreOpsTry.branch, h2] at h
          cases hloop : query_arithmetic.combine_beta_loop
              { start := 0#usize, «end» := 4#usize } powers a1 a2
              (Array.repeat 4#usize aspis_core.field.QM31.ZERO) with
          | fail e => simp [core.result.Result.Insts.CoreOpsTry.branch, hloop] at h
          | div => simp [core.result.Result.Insts.CoreOpsTry.branch, hloop] at h
          | ok z1 =>
            have hz : z1 = z := by simpa [core.result.Result.Insts.CoreOpsTry.branch, hloop] using h
            subst z1
            refine ⟨a1, a2, by simpa using h1, by simpa using h2, ?_, ?_, hloop⟩
            · exact decoder_accepted_canonical (show (104#usize : Usize).val ≤ 104 by decide) c1
                (Array.repeat 104#usize 0#u32) a1 h1
            · exact decoder_accepted_canonical (show (48#usize : Usize).val ≤ 104 by decide) c2
                (Array.repeat 48#usize 0#u32) a2 h2

#print axioms combine_accepted_inputs
end AspisV8R19.R638CombineAcceptedInputs
