import PIN2_NEWGATE_r0
import PublicSerializerFrontier431

/-! PIN2 W3b (2026-11-11). All-outcome transport of the PIN2-extracted
`public_bytes` helpers (`PIN2_NEWGATE_r0`, source 271869c946d, Stream C
emission PCXQ_E001) into the checked 4.31 serializer helpers, along the fixed
error renaming.  Same method and proofs as `ExtractedPreparationSerializerFields`,
`ExtractedPreparationSerializerLoop` and `ExtractedPreparationSerializerWhole.frontier_eq`,
restated for the PIN2 names. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1.PIN2_SerializerTransport
abbrev NewError := AspisR1PublicPreparationPIN2.aspis_core.state_only_prefix.r0.Error
abbrev OldError := AspisR1PublicSerializer.aspis_core.state_only_prefix.r0.Error
abbrev ByteVec := alloc.vec.Vec U8
abbrev Iter := core.slice.iter.Iter U32
abbrev State := Iter × ByteVec

def toError : NewError → OldError
  | .Allocation => .Allocation
  | .RowOrder expected actual => .RowOrder expected actual
  | .InvalidRow => .InvalidRow
  | .Tag row => .Tag row
  | .Length row => .Length row
  | .NonCanonical row index => .NonCanonical row index
  | .Boundary index => .Boundary index
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public

def mapStatus {α : Type} : core.result.Result α NewError → core.result.Result α OldError
  | .Ok x => .Ok x
  | .Err e => .Err (toError e)

def mapPairOutcome {α : Type} : Result (core.result.Result α NewError × ByteVec) →
    Result (core.result.Result α OldError × ByteVec)
  | .ok (status, out) => .ok (mapStatus status, out)
  | .fail e => .fail e
  | .div => .div

def mapFlow : Result (ControlFlow State (core.result.Result Unit NewError × ByteVec)) →
    Result (ControlFlow State (core.result.Result Unit OldError × ByteVec))
  | .ok (.cont state) => .ok (.cont state)
  | .ok (.done (status, out)) => .ok (.done (mapStatus status, out))
  | .fail e => .fail e
  | .div => .div

theorem fields_body_eq (it : Iter) (out : ByteVec) :
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body it out =
      mapFlow (AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body it out) := by
  unfold AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
    AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
  cases hnext : core.slice.iter.IteratorSliceIter.next it with
  | fail e => simp only [bind_tc_fail, mapFlow]
  | div => simp only [bind_tc_div, mapFlow]
  | ok pair =>
    rcases pair with ⟨value, next⟩
    cases value with
    | none => rfl
    | some value =>
      simp only [bind_tc_ok, AspisR1PublicSerializer.aspis_core.field.P,
        AspisR1PublicPreparationPIN2.aspis_core.field.P]
      change (if value >= 2147483647#u32 then
          ok (done (core.result.Result.Err
            AspisR1PublicSerializer.aspis_core.state_only_prefix.r0.Error.Public, out))
        else do
          let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
            (Array.to_slice (core.num.U32.to_le_bytes value))
          ok (cont (next, out1))) =
        mapFlow (if value >= 2147483647#u32 then
          ok (done (core.result.Result.Err
            AspisR1PublicPreparationPIN2.aspis_core.state_only_prefix.r0.Error.Public, out))
        else do
          let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
            (Array.to_slice (core.num.U32.to_le_bytes value))
          ok (cont (next, out1)))
      split
      · rfl
      · cases he : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
            (Array.to_slice (core.num.U32.to_le_bytes value)) <;> rfl

theorem fields_cont_decreases (it : Iter) (out : ByteVec) (state : State)
    (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
      it out = ok (cont state)) :
    state.1.slice.val.length - state.1.i < it.slice.val.length - it.i := by
  by_cases hi : it.i < it.slice.val.length
  · let value : U32 := it.slice.val[it.i]'hi
    let next : Iter := { it with i := it.i + 1 }
    have hnext : core.slice.iter.IteratorSliceIter.next it = ok (some value, next) := by
      simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, dif_pos hi]
      rfl
    simp only [AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body,
      hnext, bind_tc_ok] at h
    change (if value >= AspisR1PublicPreparationPIN2.aspis_core.field.P then
        ok (done (core.result.Result.Err
          AspisR1PublicPreparationPIN2.aspis_core.state_only_prefix.r0.Error.Public, out))
      else do
        let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
          (Array.to_slice (core.num.U32.to_le_bytes value))
        ok (cont (next, out1))) = ok (cont state) at h
    by_cases hbad : value >= AspisR1PublicPreparationPIN2.aspis_core.field.P
    · simp only [if_pos hbad] at h
      cases h
    · simp only [if_neg hbad] at h
      cases hext : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
          (Array.to_slice (core.num.U32.to_le_bytes value)) with
      | fail e => simp only [hext, bind_tc_fail] at h; cases h
      | div => simp only [hext, bind_tc_div] at h; cases h
      | ok out1 =>
          simp only [hext, bind_tc_ok] at h
          have hs : (next, out1) = state := ControlFlow.cont.inj (Result.ok.inj h)
          rw [← hs]
          change it.slice.val.length - (it.i + 1) < it.slice.val.length - it.i
          omega
  · have hnext : core.slice.iter.IteratorSliceIter.next it = ok (none, it) := by
      simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, dif_neg hi]
    simp only [AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body,
      hnext, bind_tc_ok] at h
    change ok (done (core.result.Result.Ok (), out)) = ok (cont state) at h
    cases h

theorem new_fields_loop_unroll (it : Iter) (out : ByteVec) :
    AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop it out = (do
      let step ← AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body it out
      match step with
      | cont (next, out1) =>
        AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop next out1
      | done result => ok result) := by
  conv_lhs =>
    unfold AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop
    rw [loop]
  cases hb : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body it out with
  | fail e => simp only [hb, bind_tc_fail]
  | div => simp only [hb, bind_tc_div]
  | ok step =>
    cases step with
    | done result => simp only [hb, bind_tc_ok]
    | cont state =>
      rcases state with ⟨next, out1⟩
      simp only [hb, bind_tc_ok]
      rfl

theorem fields_loop_eq (it : Iter) (out : ByteVec) :
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop it out =
      mapPairOutcome (AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop it out) := by
  rw [AspisR1PublicSerializer.Success431.fields_loop_unroll, new_fields_loop_unroll, fields_body_eq]
  cases h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body it out with
  | fail e => rfl
  | div => rfl
  | ok step =>
    cases step with
    | done result =>
      rcases result with ⟨status, out1⟩
      rfl
    | cont state =>
      rcases state with ⟨next, out1⟩
      change
        AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop next out1 =
          mapPairOutcome (AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop next out1)
      exact fields_loop_eq next out1
termination_by it.slice.val.length - it.i
decreasing_by exact fields_cont_decreases it out (next, out1) h

theorem fields_eq (out : ByteVec) (values : Slice U32) :
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out values =
      mapPairOutcome (AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out values) := by
  change
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop ⟨values, 0⟩ out =
      mapPairOutcome (AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop ⟨values, 0⟩ out)
  exact fields_loop_eq _ out

private theorem map_pair_bind {α : Type} (m : Result α)
    (k : α → Result (core.result.Result Unit NewError × ByteVec)) :
    mapPairOutcome (do let x ← m; k x) = (do let x ← m; mapPairOutcome (k x)) := by
  cases m <;> rfl

private theorem map_pair_ok {α : Type} (r : core.result.Result α NewError) (out : ByteVec) :
    mapPairOutcome (ok (r, out)) = ok (mapStatus r, out) := rfl

private theorem bind_map_pair {α β : Type}
    (m : Result (core.result.Result α NewError × ByteVec))
    (k : core.result.Result α OldError × ByteVec → Result β) :
    (do let x ← mapPairOutcome m; k x) =
      (do let x ← m; k (mapStatus x.1, x.2)) := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok pair => cases pair; rfl

private theorem bind_congr {α β : Type} (m : Result α) (k l : α → Result β)
    (h : ∀ x, k x = l x) :
    (do let x ← m; k x) = (do let x ← m; l x) := by
  cases m with
  | ok x => exact h x
  | fail e => rfl
  | div => rfl

private theorem bind_pair_congr {α β γ : Type} (m : Result (α × β))
    (k l : α × β → Result γ) (h : ∀ a b, k (a, b) = l (a, b)) :
    (do let x ← m; k x) = (do let x ← m; l x) := by
  apply bind_congr
  intro x
  cases x with
  | mk a b => exact h a b

macro "transport_pin2" : tactic => `(tactic|
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [fields_eq, bind_map_pair, map_pair_bind,
        uncurry_apply_pair, mapStatus, map_pair_ok,
        core.result.Result.Insts.CoreOpsTry.branch,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok])
    | (apply bind_pair_congr; intro status out; cases status)
    | (apply bind_congr; intro x))

theorem frontier_eq (out : ByteVec) (values : Array (Array U32 8#usize) 20#usize) :
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out values =
      mapPairOutcome
        (AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out values) := by
  unfold AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
    AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
  transport_pin2

/-- Successful PIN2 field write: exactly the canonical little-endian words. -/
theorem fields_success (out out' : ByteVec) (values : Slice U32)
    (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out values =
      ok (.Ok (), out')) :
    AspisR1PublicSerializer.FieldsRefinement431.canonical values.val ∧
      out'.val = out.val ++ AspisR1PublicSerializer.FieldsRefinement431.encodeWords values.val := by
  have e := fields_eq out values
  rw [h] at e
  exact AspisR1PublicSerializer.Success431.fields_success out out' values e

theorem frontier_success (out out' : ByteVec) (values : Array (Array U32 8#usize) 20#usize)
    (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out values =
      ok (.Ok (), out')) :
    AspisR1PublicSerializer.FieldsRefinement431.canonical
        ((AspisR1PublicSerializer.Frontier431.rows values).flatMap (fun s => s.val)) ∧
      out'.val = out.val ++ AspisR1PublicSerializer.FieldsRefinement431.encodeWords
        ((AspisR1PublicSerializer.Frontier431.rows values).flatMap (fun s => s.val)) := by
  have e := frontier_eq out values
  rw [h] at e
  exact AspisR1PublicSerializer.Frontier431.frontier_success out out' values e

#print axioms fields_body_eq
#print axioms fields_cont_decreases
#print axioms new_fields_loop_unroll
#print axioms fields_loop_eq
#print axioms fields_eq
#print axioms frontier_eq
#print axioms fields_success
#print axioms frontier_success
end AspisR1.PIN2_SerializerTransport
