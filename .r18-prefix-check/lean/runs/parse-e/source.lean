import ExtractedPrefixTrace

/-! Success of the actual final-E Prefix.parse links C1 and all 27 returned
frames to the input and to the actual record-step calls. No Rust/challenge/
first-read correspondence or cross-extraction canonicality is assumed. -/
namespace AspisR1.ExtractedPrefixParse
open Aeneas Aeneas.Std Result AspisR1PrefixAggregateParser
open ExtractedPrefixTrace

private theorem bind_ok_iff {α β : Type} (m : Result α)
    (f : α → Result β) (y : β) :
    (m >>= f) = ok y ↔ ∃ x, m = ok x ∧ f x = ok y := by
  cases m <;> simp

private theorem err_ite_success {α : Type} (p : Prop) [Decidable p]
    (e : r1_wire.Error) (m : Result (core.result.Result α r1_wire.Error)) (y : α) :
    (if p then ok (core.result.Result.Err e) else m) = ok (core.result.Result.Ok y) ↔
      ¬ p ∧ m = ok (core.result.Result.Ok y) := by
  by_cases hp : p <;> simp [hp]

/-- The fixed complete source trace, including C1 identity and the final
trailing-byte check; no chosen arbitrary parser witness is substituted. -/
theorem parse_success (bytes : Slice U8) (parsed : r1_wire.Prefix)
    (h : r1_wire.Prefix.parse bytes = ok (core.result.Result.Ok parsed)) :
    parsed.c1_root.val = bytes.val.take 32 ∧
      ∃ finish, RecordChain bytes rowOrder 32#usize parsed.records.val finish ∧
        finish.val = bytes.val.length := by
  unfold r1_wire.Prefix.parse at h
  obtain ⟨_, h⟩ := (err_ite_success _ _ _ _).mp h
  obtain ⟨rootSlice, hslice, h⟩ := (bind_ok_iff _ _ _).mp h
  obtain ⟨converted, hconvert, h⟩ := (bind_ok_iff _ _ _).mp h
  cases converted with
  | Err e => simp at h
  | Ok root =>
    have hroot : root.val = rootSlice.val := by
      unfold core.array.TryFromSharedArraySlice.try_from at hconvert
      split at hconvert
      · have he := core.result.Result.Ok.inj (Result.ok.inj hconvert)
        exact (congrArg (fun (a : Array U8 32#usize) => a.val) he).symm
      · simp at hconvert
    have hfirst : rootSlice.val = bytes.val.take 32 := by
      simp only [core.slice.index.Slice.index,
        core.slice.index.SliceIndexRangeToUsizeSlice,
        core.slice.index.SliceIndexRangeToUsizeSlice.index] at hslice
      split at hslice
      · have he := Result.ok.inj hslice
        have hv := congrArg (fun (s : Slice U8) => s.val) he
        simpa [List.slice] using hv.symm
      · simp at hslice
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 0#u8 32#usize) _ parsed).mp h
    rcases h with ⟨⟨r0, o1⟩, hr0, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 1#u8 o1) _ parsed).mp h
    rcases h with ⟨⟨r1, o2⟩, hr1, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 2#u8 o2) _ parsed).mp h
    rcases h with ⟨⟨r2, o3⟩, hr2, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 3#u8 o3) _ parsed).mp h
    rcases h with ⟨⟨r3, o4⟩, hr3, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 4#u8 o4) _ parsed).mp h
    rcases h with ⟨⟨r4, o5⟩, hr4, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 5#u8 o5) _ parsed).mp h
    rcases h with ⟨⟨r5, o6⟩, hr5, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 6#u8 o6) _ parsed).mp h
    rcases h with ⟨⟨r6, o7⟩, hr6, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 7#u8 o7) _ parsed).mp h
    rcases h with ⟨⟨r7, o8⟩, hr7, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 8#u8 o8) _ parsed).mp h
    rcases h with ⟨⟨r8, o9⟩, hr8, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 9#u8 o9) _ parsed).mp h
    rcases h with ⟨⟨r9, o10⟩, hr9, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 10#u8 o10) _ parsed).mp h
    rcases h with ⟨⟨r10, o11⟩, hr10, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 11#u8 o11) _ parsed).mp h
    rcases h with ⟨⟨r11, o12⟩, hr11, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 12#u8 o12) _ parsed).mp h
    rcases h with ⟨⟨r12, o13⟩, hr12, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 13#u8 o13) _ parsed).mp h
    rcases h with ⟨⟨r13, o14⟩, hr13, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 14#u8 o14) _ parsed).mp h
    rcases h with ⟨⟨r14, o15⟩, hr14, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 15#u8 o15) _ parsed).mp h
    rcases h with ⟨⟨r15, o16⟩, hr15, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 16#u8 o16) _ parsed).mp h
    rcases h with ⟨⟨r16, o17⟩, hr16, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 17#u8 o17) _ parsed).mp h
    rcases h with ⟨⟨r17, o18⟩, hr17, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 18#u8 o18) _ parsed).mp h
    rcases h with ⟨⟨r18, o19⟩, hr18, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 19#u8 o19) _ parsed).mp h
    rcases h with ⟨⟨r19, o20⟩, hr19, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 20#u8 o20) _ parsed).mp h
    rcases h with ⟨⟨r20, o21⟩, hr20, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 21#u8 o21) _ parsed).mp h
    rcases h with ⟨⟨r21, o22⟩, hr21, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 22#u8 o22) _ parsed).mp h
    rcases h with ⟨⟨r22, o23⟩, hr22, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 23#u8 o23) _ parsed).mp h
    rcases h with ⟨⟨r23, o24⟩, hr23, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 24#u8 o24) _ parsed).mp h
    rcases h with ⟨⟨r24, o25⟩, hr24, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 25#u8 o25) _ parsed).mp h
    rcases h with ⟨⟨r25, o26⟩, hr25, h⟩
    replace h := (continue_ok_iff (r1_wire.parse_record_at bytes 26#u8 o26) _ parsed).mp h
    rcases h with ⟨⟨r26, o27⟩, hr26, h⟩
    have hend : o27 = Slice.len bytes := by
      by_contra hn
      simp [hn] at h
    simp [hend] at h
    subst parsed
    refine ⟨hroot.trans hfirst, o27, ?_, ?_⟩
    · change RecordChain bytes rowOrder 32#usize
        [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26] o27
      unfold rowOrder
      apply RecordChain.cons hr0
      apply RecordChain.cons hr1
      apply RecordChain.cons hr2
      apply RecordChain.cons hr3
      apply RecordChain.cons hr4
      apply RecordChain.cons hr5
      apply RecordChain.cons hr6
      apply RecordChain.cons hr7
      apply RecordChain.cons hr8
      apply RecordChain.cons hr9
      apply RecordChain.cons hr10
      apply RecordChain.cons hr11
      apply RecordChain.cons hr12
      apply RecordChain.cons hr13
      apply RecordChain.cons hr14
      apply RecordChain.cons hr15
      apply RecordChain.cons hr16
      apply RecordChain.cons hr17
      apply RecordChain.cons hr18
      apply RecordChain.cons hr19
      apply RecordChain.cons hr20
      apply RecordChain.cons hr21
      apply RecordChain.cons hr22
      apply RecordChain.cons hr23
      apply RecordChain.cons hr24
      apply RecordChain.cons hr25
      apply RecordChain.cons hr26
      exact RecordChain.nil o27
    · simpa using congrArg UScalar.val hend

/-- Every row/frame pair in the returned complete sequence came from its
actual successful helper invocation. -/
theorem record_step_of_success (bytes : Slice U8) (parsed : r1_wire.Prefix)
    (h : r1_wire.Prefix.parse bytes = ok (core.result.Result.Ok parsed))
    (row : U8) (framed : Slice U8)
    (hm : (row, framed) ∈ rowOrder.zip parsed.records.val) :
    ∃ offset next, r1_wire.parse_record_at bytes row offset =
      ok (core.result.Result.Ok (framed, next)) := by
  obtain ⟨_, finish, hc, _⟩ := parse_success bytes parsed h
  exact hc.step_of_mem row framed hm

/-- Every returned frame passed the actual generated inner parser. -/
theorem parse_record_of_success (bytes : Slice U8) (parsed : r1_wire.Prefix)
    (h : r1_wire.Prefix.parse bytes = ok (core.result.Result.Ok parsed))
    (row : U8) (framed : Slice U8)
    (hm : (row, framed) ∈ rowOrder.zip parsed.records.val) :
    ∃ payload, r1_wire.parse_record row framed = ok (core.result.Result.Ok payload) := by
  obtain ⟨_, finish, hc, _⟩ := parse_success bytes parsed h
  exact hc.parse_record_of_mem row framed hm

end AspisR1.ExtractedPrefixParse

#print axioms AspisR1.ExtractedPrefixParse.parse_success
#print axioms AspisR1.ExtractedPrefixParse.record_step_of_success
#print axioms AspisR1.ExtractedPrefixParse.parse_record_of_success
