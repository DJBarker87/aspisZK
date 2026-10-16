import ExtractedPrefixRecordStep

/-! Compositional trace predicates and control-flow inversion for the actual
aggregate Prefix extraction. No complete Prefix theorem is asserted here. -/
namespace AspisR1.ExtractedPrefixTrace
open Aeneas Aeneas.Std Result AspisR1PrefixAggregateParser

/-- The fixed source call order, including both final circle records. -/
def rowOrder : List U8 :=
  [0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8,
   9#u8, 10#u8, 11#u8, 12#u8, 13#u8, 14#u8, 15#u8, 16#u8, 17#u8,
   18#u8, 19#u8, 20#u8, 21#u8, 22#u8, 23#u8, 24#u8, 25#u8, 26#u8]

/-- Every returned frame is linked to its actual helper invocation; the final
offset remains explicit so the caller must prove the trailing-byte check. -/
inductive RecordChain (bytes : Slice U8) :
    List U8 → Usize → List (Slice U8) → Usize → Prop where
  | nil (offset : Usize) : RecordChain bytes [] offset [] offset
  | cons {row : U8} {rows : List U8} {offset : Usize} {framed : Slice U8}
      {next : Usize} {frames : List (Slice U8)} {finish : Usize}
      (step : r1_wire.parse_record_at bytes row offset =
        ok (core.result.Result.Ok (framed, next)))
      (tail : RecordChain bytes rows next frames finish) :
      RecordChain bytes (row :: rows) offset (framed :: frames) finish

/-- Invert the exact Result/Try pattern emitted by Aeneas without unfolding the
called parser or any field arithmetic. -/
theorem continue_ok_iff {α β : Type}
    (m : Result (core.result.Result α r1_wire.Error))
    (f : α → Result (core.result.Result β r1_wire.Error)) (y : β) :
    (do
      let r ← m
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue x => f x
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          β (core.convert.FromSame r1_wire.Error) residual) =
        ok (core.result.Result.Ok y) ↔
      ∃ x, m = ok (core.result.Result.Ok x) ∧ f x = ok (core.result.Result.Ok y) := by
  cases m with
  | fail e => simp
  | div => simp
  | ok r =>
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

theorem RecordChain.length {bytes : Slice U8} {rows : List U8}
    {offset finish : Usize} {frames : List (Slice U8)}
    (h : RecordChain bytes rows offset frames finish) : frames.length = rows.length := by
  induction h <;> simp_all

/-- Membership refers to the entire zipped row/frame trace, not a selected
arbitrary parser invocation. -/
theorem RecordChain.step_of_mem {bytes : Slice U8} {rows : List U8}
    {offset finish : Usize} {frames : List (Slice U8)}
    (h : RecordChain bytes rows offset frames finish) :
    ∀ row framed, (row, framed) ∈ rows.zip frames →
      ∃ start next, r1_wire.parse_record_at bytes row start =
        ok (core.result.Result.Ok (framed, next)) := by
  induction h with
  | nil offset =>
    intro row framed hm
    simp at hm
  | @cons row rows offset framed next frames finish hstep htail ih =>
    intro selected frame hm
    simp only [List.zip_cons_cons, List.mem_cons] at hm
    rcases hm with heq | hm
    · cases heq
      exact ⟨offset, next, hstep⟩
    · exact ih selected frame hm

/-- Each frame in the complete chain passed the actual inner parser. -/
theorem RecordChain.parse_record_of_mem {bytes : Slice U8} {rows : List U8}
    {offset finish : Usize} {frames : List (Slice U8)}
    (h : RecordChain bytes rows offset frames finish) (row : U8) (framed : Slice U8)
    (hm : (row, framed) ∈ rows.zip frames) :
    ∃ payload, r1_wire.parse_record row framed = ok (core.result.Result.Ok payload) := by
  obtain ⟨start, next, hs⟩ := h.step_of_mem row framed hm
  obtain ⟨tag, size, payload, _, _, _, _, hp⟩ :=
    ExtractedPrefixRecordStep.parse_record_at_success bytes framed row start next hs
  exact ⟨payload, hp⟩

end AspisR1.ExtractedPrefixTrace

#print axioms AspisR1.ExtractedPrefixTrace.continue_ok_iff
#print axioms AspisR1.ExtractedPrefixTrace.RecordChain.length
#print axioms AspisR1.ExtractedPrefixTrace.RecordChain.step_of_mem
#print axioms AspisR1.ExtractedPrefixTrace.RecordChain.parse_record_of_mem
