import S3ActualFieldParserBridgeV1
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1GroupedPairActualFieldOpsV3.ActualLoop0SuccessReadback

open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

abbrev Loop0State := core.ops.range.Range Std.Usize × Array field.WideExact 12#usize
abbrev Loop0Output := Array field.WideExact 12#usize
abbrev Loop0BodyResult := Result (ControlFlow Loop0State Loop0Output)

def loop0ContValue (iter : core.ops.range.Range Std.Usize)
    (acc : Array field.WideExact 12#usize) : ControlFlow Loop0State Loop0Output :=
  .cont (iter, acc)

def loop0DoneValue (acc : Array field.WideExact 12#usize) :
    ControlFlow Loop0State Loop0Output := .done acc

private theorem bind_success_inv {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem loop_success_cases {α β : Type}
    (step : α → Result (ControlFlow α β)) (state : α) (out : β)
    (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧
        Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok cf =>
    cases cf with
    | done result => simp [hs] at h; subst result; exact Or.inl rfl
    | cont stateNext => simp [hs] at h; exact Or.inr ⟨stateNext, rfl, h⟩

/-- A successful emitted first-loop body at an active range position must have
read the group, old coefficient, input coefficient, performed the selected add,
and updated the accumulator. -/
theorem loop0_body_success_inversion
    (bytes : Slice Std.U8)
    (iter : core.ops.range.Range Std.Usize)
    (acc : Array field.WideExact 12#usize)
    (iterNext : core.ops.range.Range Std.Usize)
    (accNext : Array field.WideExact 12#usize)
    (hbody : weights.s2_grouped_inactive_pair_loop0.body actualOperations bytes iter acc =
      .ok (loop0ContValue iterNext accNext)) :
    ∃ (j : Std.Usize) (groupByte : Std.U8) (group : Std.Usize)
      (oldCoeff inputCoeff newCoeff : field.WideExact),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some j, iterNext) ∧
      Array.index_usize weights.S2_INACTIVE_GROUPS j = .ok groupByte ∧
      lift (UScalar.cast .Usize groupByte) = .ok group ∧
      Array.index_usize acc group = .ok oldCoeff ∧
      actualOperations.decodeField bytes j = .ok inputCoeff ∧
      actualOperations.add oldCoeff inputCoeff = .ok newCoeff ∧
      Array.update acc group newCoeff = .ok accNext := by
  unfold weights.s2_grouped_inactive_pair_loop0.body at hbody
  obtain ⟨pair, hnext, hrest⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter)
    (fun pair : Option Std.Usize × core.ops.range.Range Std.Usize => match pair.1 with
      | none => .ok (loop0DoneValue acc)
      | some j => do
          let groupByte ← Array.index_usize weights.S2_INACTIVE_GROUPS j
          let group ← lift (UScalar.cast .Usize groupByte)
          let oldCoeff ← Array.index_usize acc group
          let inputCoeff ← actualOperations.decodeField bytes j
          let newCoeff ← actualOperations.add oldCoeff inputCoeff
          let accNext ← Array.update acc group newCoeff
          .ok (loop0ContValue pair.2 accNext)) (loop0ContValue iterNext accNext) hbody
  rcases pair with ⟨option, iterResult⟩
  cases option with
  | none => cases hrest
  | some j =>
      obtain ⟨groupByte, hgroup, hrest⟩ := bind_success_inv
        (Array.index_usize weights.S2_INACTIVE_GROUPS j)
        (fun groupByte => do
          let group ← lift (UScalar.cast .Usize groupByte)
          let oldCoeff ← Array.index_usize acc group
          let inputCoeff ← actualOperations.decodeField bytes j
          let newCoeff ← actualOperations.add oldCoeff inputCoeff
          let accNext ← Array.update acc group newCoeff
          .ok (loop0ContValue iterResult accNext)) (loop0ContValue iterNext accNext) hrest
      obtain ⟨group, hcast, hrest⟩ := bind_success_inv
        (lift (UScalar.cast .Usize groupByte))
        (fun group => do
          let oldCoeff ← Array.index_usize acc group
          let inputCoeff ← actualOperations.decodeField bytes j
          let newCoeff ← actualOperations.add oldCoeff inputCoeff
          let accNext ← Array.update acc group newCoeff
          .ok (loop0ContValue iterResult accNext)) (loop0ContValue iterNext accNext) hrest
      obtain ⟨oldCoeff, hold, hrest⟩ := bind_success_inv
        (Array.index_usize acc group)
        (fun oldCoeff => do
          let inputCoeff ← actualOperations.decodeField bytes j
          let newCoeff ← actualOperations.add oldCoeff inputCoeff
          let accNext ← Array.update acc group newCoeff
          .ok (loop0ContValue iterResult accNext)) (loop0ContValue iterNext accNext) hrest
      obtain ⟨inputCoeff, hin, hrest⟩ := bind_success_inv
        (actualOperations.decodeField bytes j)
        (fun inputCoeff => do
          let newCoeff ← actualOperations.add oldCoeff inputCoeff
          let accNext ← Array.update acc group newCoeff
          .ok (loop0ContValue iterResult accNext)) (loop0ContValue iterNext accNext) hrest
      obtain ⟨newCoeff, hadd, hrest⟩ := bind_success_inv
        (actualOperations.add oldCoeff inputCoeff)
        (fun newCoeff => do
          let accNext ← Array.update acc group newCoeff
          .ok (loop0ContValue iterResult accNext)) (loop0ContValue iterNext accNext) hrest
      obtain ⟨updated, hupdate, hfinal⟩ := bind_success_inv
        (Array.update acc group newCoeff)
        (fun updated => .ok (loop0ContValue iterResult updated))
        (loop0ContValue iterNext accNext) hrest
      have hpair : iterResult = iterNext ∧ updated = accNext := by
        cases hfinal
        exact ⟨rfl, rfl⟩
      rcases hpair with ⟨rfl, rfl⟩
      exact ⟨j, groupByte, group, oldCoeff, inputCoeff, newCoeff,
        hnext, hgroup, hcast, hold, hin, hadd, hupdate⟩

private theorem loop0_body_done_impossible_of_next_some
    (bytes : Slice Std.U8)
    (iter : core.ops.range.Range Std.Usize)
    (acc out : Array field.WideExact 12#usize)
    (j : Std.Usize) (iterNext : core.ops.range.Range Std.Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j, iterNext))
    (hdone : weights.s2_grouped_inactive_pair_loop0.body actualOperations bytes iter acc =
      .ok (loop0DoneValue out)) : False := by
  unfold weights.s2_grouped_inactive_pair_loop0.body at hdone
  rw [hnext] at hdone
  simp only [bind_tc_ok] at hdone
  obtain ⟨groupByte, hgroup, hrest⟩ := bind_success_inv
    (Array.index_usize weights.S2_INACTIVE_GROUPS j)
    (fun groupByte => do
      let group ← lift (UScalar.cast .Usize groupByte)
      let oldCoeff ← Array.index_usize acc group
      let inputCoeff ← actualOperations.decodeField bytes j
      let newCoeff ← actualOperations.add oldCoeff inputCoeff
      let accNext ← Array.update acc group newCoeff
      .ok (loop0ContValue iterNext accNext)) (loop0DoneValue out) hdone
  obtain ⟨group, hcast, hrest⟩ := bind_success_inv
    (lift (UScalar.cast .Usize groupByte))
    (fun group => do
      let oldCoeff ← Array.index_usize acc group
      let inputCoeff ← actualOperations.decodeField bytes j
      let newCoeff ← actualOperations.add oldCoeff inputCoeff
      let accNext ← Array.update acc group newCoeff
      .ok (loop0ContValue iterNext accNext)) (loop0DoneValue out) hrest
  obtain ⟨oldCoeff, hold, hrest⟩ := bind_success_inv
    (Array.index_usize acc group)
    (fun oldCoeff => do
      let inputCoeff ← actualOperations.decodeField bytes j
      let newCoeff ← actualOperations.add oldCoeff inputCoeff
      let accNext ← Array.update acc group newCoeff
      .ok (loop0ContValue iterNext accNext)) (loop0DoneValue out) hrest
  obtain ⟨inputCoeff, hin, hrest⟩ := bind_success_inv
    (actualOperations.decodeField bytes j)
    (fun inputCoeff => do
      let newCoeff ← actualOperations.add oldCoeff inputCoeff
      let accNext ← Array.update acc group newCoeff
      .ok (loop0ContValue iterNext accNext)) (loop0DoneValue out) hrest
  obtain ⟨newCoeff, hadd, hrest⟩ := bind_success_inv
    (actualOperations.add oldCoeff inputCoeff)
    (fun newCoeff => do
      let accNext ← Array.update acc group newCoeff
      .ok (loop0ContValue iterNext accNext)) (loop0DoneValue out) hrest
  obtain ⟨updated, hupdate, hfinal⟩ := bind_success_inv
    (Array.update acc group newCoeff)
    (fun updated => .ok (loop0ContValue iterNext updated)) (loop0DoneValue out) hrest
  cases hfinal

/-- Any successful execution of the actual first accumulation loop must have
successfully decoded every requested index in its remaining half-open range.
The result keeps the exact parser slice witness for each index. -/
theorem loop0_success_parser_reads
    (bytes : Slice Std.U8)
    (iter : core.ops.range.Range Std.Usize)
    (acc : Array field.WideExact 12#usize)
    (result : Array field.WideExact 12#usize)
    (hstart : iter.start.val ≤ 64)
    (hend : iter.end.val = 64)
    (hrun : weights.s2_grouped_inactive_pair_loop0 actualOperations iter bytes acc =
      .ok result) :
    ∀ n : Nat, iter.start.val ≤ n → n < 64 →
      ∃ (j : Std.Usize) (inputCoeff : field.WideExact)
        (raw : AspisR1RecordParser.field.wide_exact.WideExact)
        (start next finish : Std.Usize) (selected : Slice Std.U8),
        j.val = n ∧
        actualOperations.decodeField bytes j = .ok inputCoeff ∧
        AspisR1WeightsFieldCurrent.weights.field
          AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes j =
            .ok raw ∧
        (j * 32#usize : Result Usize) = .ok start ∧
        (j + 1#usize : Result Usize) = .ok next ∧
        (next * 32#usize : Result Usize) = .ok finish ∧
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
          { start := start, «end» := finish } = .ok selected ∧
        AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected =
          .ok (some raw) := by
  induction hfuel : 64 - iter.start.val generalizing iter acc result hstart hend hrun with
  | zero =>
      have hstart64 : iter.start.val = 64 := by omega
      intro n hn hn64
      omega
  | succ fuel ih =>
      have hactive : iter.start.val < iter.end.val := by rw [hend]; omega
      let step : Loop0State → Result (ControlFlow Loop0State Loop0Output) :=
        fun s => weights.s2_grouped_inactive_pair_loop0.body actualOperations bytes s.1 s.2
      have hloop : Aeneas.Std.loop step (iter, acc) = .ok result := by
        change Aeneas.Std.loop step (iter, acc) = .ok result
        simpa [weights.s2_grouped_inactive_pair_loop0, step] using hrun
      rcases loop_success_cases step (iter, acc) result hloop with hdone | hcont
      · change weights.s2_grouped_inactive_pair_loop0.body actualOperations bytes iter acc =
          .ok (.done result) at hdone
        have hnextSpec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
          (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intros; rfl) (by intros; rfl) iter hactive
        obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists hnextSpec
        rcases pair with ⟨option, iterNext⟩
        rcases hpost with ⟨hopt, _hstartNext, _hendNext⟩
        have hnextSome : core.iter.range.IteratorRange.next
            core.iter.range.StepUsize iter = .ok (some iter.start, iterNext) := by
          rw [← hopt]
          exact hnext
        exact False.elim
          (loop0_body_done_impossible_of_next_some bytes iter acc result
            iter.start iterNext hnextSome hdone)
      · rcases hcont with ⟨stateNext, hbody, htail⟩
        rcases stateNext with ⟨iterNext, accNext⟩
        change weights.s2_grouped_inactive_pair_loop0.body actualOperations bytes iter acc =
          .ok (loop0ContValue iterNext accNext) at hbody
        obtain ⟨j, groupByte, group, oldCoeff, inputCoeff, newCoeff,
          hnext, _hgroup, _hcast, _hold, hdecode, _hadd, _hupdate⟩ :=
          loop0_body_success_inversion bytes iter acc iterNext accNext hbody
        have hnextSpec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
          (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intros; rfl) (by intros; rfl) iter hactive
        obtain ⟨pair, hnextSpecEq, hpost⟩ := WP.spec_imp_exists hnextSpec
        rcases pair with ⟨option, iterSpec⟩
        rcases hpost with ⟨hopt, hstartNext, hendNext⟩
        have hpair : (some j, iterNext) = (option, iterSpec) :=
          Result.ok.inj (hnext.symm.trans hnextSpecEq)
        rcases Prod.mk.inj hpair with ⟨hoption, hiter⟩
        have hjOption : option = some iter.start := hopt
        have hj : j = iter.start := Option.some.inj (hoption.trans hjOption)
        subst j
        subst iterSpec
        have hstartNextVal : iterNext.start.val = iter.start.val + 1 := hstartNext
        have hendNextVal : iterNext.end.val = 64 := by
          have := congrArg UScalar.val hendNext
          rw [hend] at this
          exact this
        have htailRun : weights.s2_grouped_inactive_pair_loop0 actualOperations
            iterNext bytes accNext = .ok result := by
          simpa [step, weights.s2_grouped_inactive_pair_loop0] using htail
        intro n hn hn64
        by_cases hcurrent : n = iter.start.val
        · have hread := decodeField_success_parser_readback bytes iter.start inputCoeff hdecode
          rcases hread with ⟨raw, start, next, finish, selected,
            hparser, hi, hnxt, hf, hs, hdecodeRaw, hout⟩
          refine ⟨iter.start, inputCoeff, raw, start, next, finish, selected,
            ?_, ?_, hparser, hi, hnxt, hf, hs, hdecodeRaw⟩
          · exact hcurrent.symm
          · exact hdecode
        · have hnextLower : iterNext.start.val ≤ n := by rw [hstartNextVal]; omega
          have hnextFuel : 64 - iterNext.start.val = fuel := by
            rw [hstartNextVal]
            omega
          obtain ⟨j2, inputCoeff2, raw2, start2, next2, finish2, selected2,
            hj2, hdecode2, hparser2, hi2, hnxt2, hf2, hs2, hraw2⟩ :=
            ih iterNext accNext result (by omega) hendNextVal htailRun
              hnextFuel n hnextLower hn64
          exact ⟨j2, inputCoeff2, raw2, start2, next2, finish2, selected2,
            hj2, hdecode2, hparser2, hi2, hnxt2, hf2, hs2, hraw2⟩

/-- A successful actual grouped-pair helper necessarily passed through all 64
field reads of loop 0. This is the caller-facing success inversion: it does not
take per-index parser success as a premise. -/
theorem grouped_pair_success_supplies_parser_reads
    (bytes : Slice Std.U8)
    (low : Array field.WideExact 16#usize)
    (out : field.WideExact)
    (h : weights.s2_grouped_inactive_pair actualOperations bytes low = .ok out) :
    ∀ n : Nat, n < 64 →
      ∃ (j : Std.Usize) (inputCoeff : field.WideExact)
        (raw : AspisR1RecordParser.field.wide_exact.WideExact)
        (start next finish : Std.Usize) (selected : Slice Std.U8),
        j.val = n ∧
        actualOperations.decodeField bytes j = .ok inputCoeff ∧
        AspisR1WeightsFieldCurrent.weights.field
          AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes j =
            .ok raw ∧
        (j * 32#usize : Result Usize) = .ok start ∧
        (j + 1#usize : Result Usize) = .ok next ∧
        (next * 32#usize : Result Usize) = .ok finish ∧
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
          { start := start, «end» := finish } = .ok selected ∧
        AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected =
          .ok (some raw) := by
  unfold weights.s2_grouped_inactive_pair at h
  change (do
    let coefficients1 ← weights.s2_grouped_inactive_pair_loop0 actualOperations
      { start := 0#usize, «end» := 64#usize } bytes
      (Array.repeat 12#usize field.WideExact.ZERO)
    weights.s2_grouped_inactive_pair_loop1 actualOperations
      { start := 0#usize, «end» := 12#usize } low coefficients1
      field.WideExact.ZERO) = .ok out at h
  obtain ⟨coefficients1, hloop0, _hloop1⟩ := bind_success_inv
    (weights.s2_grouped_inactive_pair_loop0 actualOperations
      { start := 0#usize, «end» := 64#usize } bytes
      (Array.repeat 12#usize field.WideExact.ZERO))
    (fun coefficients1 => weights.s2_grouped_inactive_pair_loop1 actualOperations
      { start := 0#usize, «end» := 12#usize } low coefficients1
      field.WideExact.ZERO) out h
  have hfields := loop0_success_parser_reads bytes
    { start := 0#usize, «end» := 64#usize }
    (Array.repeat 12#usize field.WideExact.ZERO) coefficients1
    (by scalar_tac) (by scalar_tac) hloop0
  intro n hn
  exact hfields n (by scalar_tac) hn

#print axioms loop0_success_parser_reads
#print axioms grouped_pair_success_supplies_parser_reads

#print axioms loop0_body_success_inversion

end AspisR1GroupedPairActualFieldOpsV3.ActualLoop0SuccessReadback
