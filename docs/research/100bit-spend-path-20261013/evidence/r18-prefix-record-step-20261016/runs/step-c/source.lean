import AspisR1PrefixAggregateParser.Funs

/-!
One successful record step of the exact aggregate Prefix extraction.
This theorem does not reuse another generated namespace, unfold the field
validator, or assert the complete 27-record Prefix/Rust correspondence.
-/
namespace AspisR1.ExtractedPrefixRecordStep
open Aeneas Aeneas.Std Result AspisR1PrefixAggregateParser

private theorem bind_ok_iff {α β : Type} (m : Result α)
    (f : α → Result β) (y : β) :
    (m >>= f) = ok y ↔ ∃ x, m = ok x ∧ f x = ok y := by
  cases m <;> simp

private theorem add_ok_val (a b c : Usize) (h : a + b = ok c) :
    c.val = a.val + b.val := by
  have he := UScalar.add_equiv a b
  rw [h] at he
  exact he.2.1

/-- Success exposes the exact selected input slice, next offset and successful
inner parser call. No canonicality or validation premise is added. -/
theorem parse_record_at_success (bytes framed : Slice U8) (row : U8)
    (offset next : Usize)
    (h : r1_wire.parse_record_at bytes row offset =
      ok (core.result.Result.Ok (framed, next))) :
    ∃ tag size payload,
      r1_wire.row_shape row = ok (some (tag, size)) ∧
      next.val = offset.val + 5 + size.val ∧
      next.val ≤ bytes.val.length ∧
      framed.val = (bytes.val.drop offset.val).take (5 + size.val) ∧
      r1_wire.parse_record row framed = ok (core.result.Result.Ok payload) := by
  unfold r1_wire.parse_record_at at h
  obtain ⟨shape, hshape, h⟩ := (bind_ok_iff _ _ _).mp h
  cases shape with
  | none => simp [core.option.Option.unwrap, Result.ofOption] at h
  | some pair =>
    rcases pair with ⟨tag, size⟩
    simp only [core.option.Option.unwrap, Result.ofOption, bind_tc_ok] at h
    obtain ⟨length, hlength, h⟩ := (bind_ok_iff _ _ _).mp h
    obtain ⟨finish, hfinish, h⟩ := (bind_ok_iff _ _ _).mp h
    obtain ⟨maybe, hget, h⟩ := (bind_ok_iff _ _ _).mp h
    cases maybe with
    | none =>
      simp [AspisR1PrefixAggregateParser.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | some actual =>
      simp only [AspisR1PrefixAggregateParser.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      obtain ⟨parsed, hparse, h⟩ := (bind_ok_iff _ _ _).mp h
      cases parsed with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
      | Ok payload =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
          Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨heq, hoff⟩
        subst actual
        subst finish
        have hb : offset.val ≤ next.val ∧ next.val ≤ bytes.val.length := by
          by_contra hn
          simp [core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice,
            core.slice.index.SliceIndexRangeUsizeSlice.get, hn] at hget
        have hs : bytes.val.slice offset.val next.val = framed.val := by
          have he := hget
          simp only [core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice,
            core.slice.index.SliceIndexRangeUsizeSlice.get, UScalar.le_equiv,
            Slice.length, hb, true_and, ↓reduceIte,
            Result.ok.injEq, Option.some.injEq] at he
          exact congrArg (fun (s : Slice U8) => s.val) he
        have hl : length.val = 5 + size.val := by
          simpa using add_ok_val _ _ _ hlength
        have hn : next.val = offset.val + 5 + size.val := by
          simpa [hl, Nat.add_assoc] using add_ok_val _ _ _ hfinish
        refine ⟨tag, size, payload, hshape, hn, ?_, ?_, hparse⟩
        · simpa using hb.2
        · simpa [List.slice, hn, Nat.add_assoc] using hs.symm

end AspisR1.ExtractedPrefixRecordStep

#print axioms AspisR1.ExtractedPrefixRecordStep.parse_record_at_success
