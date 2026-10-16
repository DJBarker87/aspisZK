import AspisR1ViewParseProbe.CleanParameterizedParse
import AspisR1ViewParseProbe.FoldedOffsetsWidth

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1ViewParseProbe.ParseShapeRound1Root

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- A successful shape parse with the two-folds variant has the exact 224-byte
round-one source interval. -/
theorem parse_shape_round1_root (bytes : Slice Std.U8) (shape : verifier.ViewShape)
    (hparse : verifier.View.parse_shape bytes = ok (.Ok shape))
    (hfold : transport.Variant.folds shape.variant = ok 2#usize) :
    ∃ base, shape.folded_root_start = some base ∧
      shape.round1_end.val - shape.round1_start.val = 224 := by
  unfold verifier.View.parse_shape at hparse
  by_cases hshort : Slice.len bytes < verifier.HEADER
  · simp only [hshort, if_pos, bind_tc_ok] at hparse
    cases hparse
  · simp only [hshort, if_neg] at hparse
    obtain ⟨magic, hmagic, hparse⟩ := bind_success _ _ _ hparse
    obtain ⟨badMagic, hbadMagic, hparse⟩ := bind_success _ _ _ hparse
    split at hparse <;> try cases hparse
    obtain ⟨reserved, hreserved, hparse⟩ := bind_success _ _ _ hparse
    obtain ⟨iter, hiter, hparse⟩ := bind_success _ _ _ hparse
    obtain ⟨anyResult, hany, hparse⟩ := bind_success _ _ _ hparse
    rcases anyResult with ⟨badReserved, anyState⟩
    change (if badReserved = true then _ else _) = _ at hparse
    split at hparse <;> try cases hparse
    obtain ⟨tag, htag, hparse⟩ := bind_success _ _ _ hparse
    obtain ⟨variantOpt, hvariantOpt, hparse⟩ := bind_success _ _ _ hparse
    obtain ⟨parsedVariant, hparsedVariant, hparse⟩ := bind_success _ _ _ hparse
    obtain ⟨flow, hflow, hparse⟩ := bind_success _ _ _ hparse
    cases flow with
    | Break residual =>
        cases residual with
        | Ok impossible => cases impossible
        | Err e =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hparse
    | Continue variant =>
      obtain ⟨proofLen, hproofLen, hparse⟩ := bind_success _ _ _ hparse
      split at hparse
      · cases hparse
      ·
        obtain ⟨semanticLen, hsemanticLen, hparse⟩ := bind_success _ _ _ hparse
        obtain ⟨at1, hat1, hparse⟩ := bind_success _ _ _ hparse
        obtain ⟨y1Width, hy1Width, hparse⟩ := bind_success _ _ _ hparse
        obtain ⟨at2, hat2, hparse⟩ := bind_success _ _ _ hparse
        obtain ⟨at3, hat3, hparse⟩ := bind_success _ _ _ hparse
        obtain ⟨round0Bytes, hround0Bytes, hparse⟩ := bind_success _ _ _ hparse
        obtain ⟨inactiveOpt, hinactiveOpt, hparse⟩ := bind_success _ _ _ hparse
        obtain ⟨parsedInactive, hparsedInactive, hparse⟩ := bind_success _ _ _ hparse
        obtain ⟨flowInactive, hflowInactive, hparse⟩ := bind_success _ _ _ hparse
        cases flowInactive with
        | Break residual =>
            cases residual with
            | Ok impossible => cases impossible
            | Err e =>
                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at hparse
        | Continue inactive =>
          obtain ⟨foldWidth, hfoldWidth, hparse⟩ := bind_success _ _ _ hparse
          obtain ⟨base, hbase, hparse⟩ := bind_success _ _ _ hparse
          obtain ⟨folds, hfolds, hparse⟩ := bind_success _ _ _ hparse
          obtain ⟨offsets, hoffsets, hparse⟩ := bind_success _ _ _ hparse
          obtain ⟨afterFold, hafterFold, hparse⟩ := bind_success _ _ _ hparse
          obtain ⟨finalLen, hfinalLen, hparse⟩ := bind_success _ _ _ hparse
          obtain ⟨finalBytes, hfinalBytes, hparse⟩ := bind_success _ _ _ hparse
          obtain ⟨queryStart, hqueryStart, hparse⟩ := bind_success _ _ _ hparse
          have hinner :
              (core.result.Result.Ok
                { variant := variant, inactive := inactive,
                  semantic_start := verifier.HEADER, semantic_end := at1,
                  y1_start := at1, y1_end := at2,
                  round0_start := at3, round0_end := base,
                  folded_root_start := offsets.1,
                  round1_start := offsets.2.1,
                  round1_end := offsets.2.2.1,
                  final_start := afterFold, final_end := queryStart,
                  query_start := queryStart } :
                core.result.Result verifier.ViewShape verifier.Error) =
              (core.result.Result.Ok shape :
                core.result.Result verifier.ViewShape verifier.Error) := by
            exact Result.ok.inj hparse
          have hrecord :
              ({ variant := variant, inactive := inactive,
                  semantic_start := verifier.HEADER, semantic_end := at1,
                  y1_start := at1, y1_end := at2,
                  round0_start := at3, round0_end := base,
                  folded_root_start := offsets.1,
                  round1_start := offsets.2.1,
                  round1_end := offsets.2.2.1,
                  final_start := afterFold, final_end := queryStart,
                  query_start := queryStart } : verifier.ViewShape) = shape :=
            by injection hinner with hrec
          have hvariant : variant = shape.variant :=
            congrArg (fun x : verifier.ViewShape => x.variant) hrecord
          have hfoldVariant : transport.Variant.folds variant = ok 2#usize := by
            simpa [hvariant] using hfold
          have hfoldEq : folds = 2#usize := by
            have heq := hfolds.symm.trans hfoldVariant
            injection heq
          have hoffsetTrue : verifier.folded_offsets base true =
              ok (offsets.1, offsets.2.1, offsets.2.2.1, offsets.2.2.2) := by
            simpa [hfoldEq] using hoffsets
          have hroot : offsets.1 = some base := by
            have htmp := hoffsetTrue
            unfold verifier.folded_offsets at htmp
            obtain ⟨i, hi, htmp⟩ := bind_success _ _ _ htmp
            obtain ⟨j, hj, htmp⟩ := bind_success _ _ _ htmp
            have ht := Result.ok.inj htmp
            simp only [Prod.mk.injEq, Option.some.injEq] at ht
            exact ht.1.symm
          rw [hroot] at hoffsetTrue
          have hwidth := AspisR1ViewParseProbe.FoldedOffsetsWidth.folded_offsets_round1_width
            base offsets.2.1 offsets.2.2.1 offsets.2.2.2 hoffsetTrue
          have hs : offsets.2.1 = shape.round1_start :=
            congrArg (fun x : verifier.ViewShape => x.round1_start) hrecord
          have he : offsets.2.2.1 = shape.round1_end :=
            congrArg (fun x : verifier.ViewShape => x.round1_end) hrecord
          rw [hs, he] at hwidth
          have hsroot : shape.folded_root_start = offsets.1 :=
            (congrArg (fun x : verifier.ViewShape => x.folded_root_start) hrecord).symm
          refine ⟨base, ?_, hwidth⟩
          rw [hsroot, hroot]

#print axioms parse_shape_round1_root

end AspisR1ViewParseProbe.ParseShapeRound1Root
