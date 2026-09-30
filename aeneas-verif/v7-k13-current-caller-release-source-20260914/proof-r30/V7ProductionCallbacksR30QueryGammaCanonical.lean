import V7ProductionCallbacksR30PackedGammaCanonical
import V7ProductionCallbacksR30ArrayCanonical
import V7ProductionCallbacksR29.FunsChunk10

/-! Canonicality through the literal sixteen-query openings loop. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30QueryGammaCanonical
open V7ProductionCallbacksR30MutableCanonical
open V7ProductionCallbacksR30ArrayCanonical
open V7ProductionCallbacksR30PackedGammaCanonical
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev QM31 := V7ProductionCallbacksR30Qm31Canonical.CallbackQM31
abbrev Row := Array QM31 4#usize
abbrev Rows := Array Row 16#usize
abbrev Wire := V7ProductionCallbacksR29.aspis_core.v7_onefold.V7CompactOneFoldWire
abbrev Powers := V7ProductionCallbacksR29.aspis_core.state_only_spend_query.StateOnlySpendQueryPowers
abbrev Hash := Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)
abbrev Iter := core.array.iter.IntoIter (Std.U32 × Std.Usize) 16#usize
abbrev Entries := alloc.vec.Vec (Std.U32 × Array Std.U8 26#usize × Array Std.U8 26#usize)
abbrev State := Iter × Rows × Entries
abbrev Output := core.result.Result Rows V7ProductionCallbacksR29.aspis_core.v6_onefold.V6WireError

local instance : Inhabited QM31 := ⟨V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO⟩
local instance : Inhabited Row := ⟨Array.repeat 4#usize V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO⟩

def RowCanonical (row : Row) := SliceAll GeneratedCanonicalQM31 row.to_slice
def RowsCanonical (rows : Rows) := SliceAll RowCanonical rows.to_slice

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private def body (wire : Wire) (hash : Hash) (powers : Powers) (state : State) :
    Result (ControlFlow State Output) :=
  V7ProductionCallbacksR29.aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings_loop.body
    wire hash powers state.1 state.2.1 state.2.2

private def FlowCanonical (flow : ControlFlow State Output) : Prop :=
  match flow with
  | cont next => RowsCanonical next.2.1
  | done result => ∀ output, result = .Ok output → RowsCanonical output

private theorem body_preserves_canonical
    (wire : Wire) (hash : Hash) (powers : Powers) (state : State)
    (flow : ControlFlow State Output)
    (canonical : RowsCanonical state.2.1)
    (edge : body wire hash powers state = ok flow) : FlowCanonical flow := by
  unfold body at edge
  unfold V7ProductionCallbacksR29.aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings_loop.body at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨⟨option, nextIter⟩, nextRun, edge⟩ := edge
  cases option with
  | none =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨⟨valid, _, _⟩, merkleRun, edge⟩ := edge
      cases valid <;> simp only [Bool.false_eq_true, ↓reduceIte] at edge
      · cases edge
        intro output impossible
        cases impossible
      · cases edge
        intro output exactOutput
        cases exactOutput
        exact canonical
  | some pair =>
      rcases pair with ⟨query, ordinal⟩
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨queryOption, queryRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨queryResult, queryResultRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨queryBranch, queryBranchRun, edge⟩ := edge
      cases queryResult with
      | Err error =>
          have branchExact : queryBranch = .Break (.Err error) := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok.inj queryBranchRun).symm
          rw [branchExact] at edge
          simp only [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from, bind_tc_ok] at edge
          cases edge
          intro output impossible
          cases impossible
      | Ok queryView =>
          have branchExact : queryBranch = .Continue queryView := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok.inj queryBranchRun).symm
          rw [branchExact] at edge
          simp only at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨gammaResult, gammaRun, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨gammaBranch, gammaBranchRun, edge⟩ := edge
          cases gammaResult with
          | Err error =>
              have branchExact : gammaBranch = .Break (.Err error) := by
                simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok.inj gammaBranchRun).symm
              rw [branchExact] at edge
              simp only [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from, bind_tc_ok] at edge
              cases edge
              intro output impossible
              cases impossible
          | Ok row =>
              have rowCanonical := (successful_packed_gamma_canonical
                queryView.c1_packed queryView.c2_packed powers row gammaRun).1
              have branchExact : gammaBranch = .Continue row := by
                simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok.inj gammaBranchRun).symm
              rw [branchExact] at edge
              simp only at edge
              rw [bind_eq_ok_iff] at edge
              obtain ⟨updated, updateRun, edge⟩ := edge
              rw [bind_eq_ok_iff] at edge
              obtain ⟨hash0, hash0Run, edge⟩ := edge
              rw [bind_eq_ok_iff] at edge
              obtain ⟨hash1, hash1Run, edge⟩ := edge
              rw [bind_eq_ok_iff] at edge
              obtain ⟨entries, entriesRun, edge⟩ := edge
              cases edge
              exact array_update_all RowCanonical state.2.1 updated ordinal row canonical rowCanonical updateRun

private theorem trace_preserves_canonical
    (wire : Wire) (hash : Hash) (powers : Powers) {state : State} {result : Output}
    (trace : ExactLoopTrace (body wire hash powers) state result) :
    RowsCanonical state.2.1 → ∀ output, result = .Ok output → RowsCanonical output := by
  induction trace with
  | done edge =>
      intro canonical
      exact body_preserves_canonical wire hash powers _ _ canonical edge
  | cont edge tail ih =>
      intro canonical
      exact ih (body_preserves_canonical wire hash powers _ _ canonical edge)

theorem successful_query_gamma_loop_canonical
    (wire : Wire) (hash : Hash) (powers : Powers) (iter : Iter)
    (initial output : Rows) (entries : Entries)
    (canonical : RowsCanonical initial)
    (run : V7ProductionCallbacksR29.aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings_loop
      wire iter hash powers initial entries = ok (.Ok output)) : RowsCanonical output := by
  have loopRun : loop (body wire hash powers) (iter, initial, entries) = ok (.Ok output) := run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace (body wire hash powers)
    (iter, initial, entries) (.Ok output) loopRun
  exact trace_preserves_canonical wire hash powers trace canonical output rfl

#print axioms successful_query_gamma_loop_canonical

private theorem zero_row_canonical :
    RowCanonical (Array.repeat 4#usize V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO) := by
  intro index bound
  have indexBound : index < 4 := by simpa [Array.to_slice, Array.repeat] using bound
  have entryExact :
      (List.replicate 4 V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO)[index]! =
        V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO := by
    simp only [List.getElem!_eq_getElem?_getD,
      List.getElem?_replicate_of_lt indexBound, Option.getD_some]
  change GeneratedCanonicalQM31 ((List.replicate 4
    V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO)[index]!)
  rw [entryExact]
  norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
    V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem zero_rows_canonical :
    RowsCanonical (Array.repeat 16#usize (Array.repeat 4#usize
      V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO)) := by
  intro index bound
  have indexBound : index < 16 := by simpa [Array.to_slice, Array.repeat] using bound
  let zeroRow : Row := Array.repeat 4#usize V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO
  change RowCanonical ((List.replicate 16 zeroRow)[index]!)
  have entryExact :
      (List.replicate 16 zeroRow)[index]! = zeroRow := by
    simp only [List.getElem!_eq_getElem?_getD,
      List.getElem?_replicate_of_lt indexBound, Option.getD_some]
  rw [entryExact]
  exact zero_row_canonical

theorem successful_query_gamma_canonical
    (hash : Hash) (wire : Wire) (queries : Array Std.U32 16#usize)
    (powers : Powers) (output : Rows)
    (run : V7ProductionCallbacksR29.aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings
      hash wire queries powers = ok (.Ok output)) : RowsCanonical output := by
  unfold V7ProductionCallbacksR29.aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨order, orderRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨⟨slice, toArray⟩, sliceRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨sorted, sortRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨lastIndex, lastIndexRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨⟨lastQuery, lastOrdinal⟩, lastRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨domainSize, domainRun, run⟩ := run
  split at run
  · cases run
  · rw [bind_eq_ok_iff] at run
    obtain ⟨sortedSlice, sortedSliceRun, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨windows, windowsRun, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨⟨duplicate, _⟩, duplicateRun, run⟩ := run
    cases duplicate
    · simp only [Bool.false_eq_true, ↓reduceIte] at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨iter, iterRun, run⟩ := run
      exact successful_query_gamma_loop_canonical wire hash powers iter _ output _ zero_rows_canonical run
    · cases run

#print axioms successful_query_gamma_canonical
end V7ProductionCallbacksR30QueryGammaCanonical
