import Port5Q2_ReaderRaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderValidate
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
def validate_loop.body
  (queries : Array Std.U32 22#usize) (i : Std.Usize) :
  Result (ControlFlow Std.Usize (Option (core.result.Result Unit
    verifier.Error)))
  := do
  let s ← lift (Array.to_slice queries)
  let i1 := Slice.len s
  if i < i1
  then
    let q ← Array.index_usize queries i
    let i2 ← lift (Std.U32.wrapping_shl 1#u32 18#u32)
    if q >= i2
    then ok (done none)
    else
      let s1 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) queries
          { «end» := i }
      let b ← core.slice.Slice.contains core.cmp.PartialEqU32 s1 q
      if b
      then ok (done none)
      else let i3 ← lift (Std.Usize.wrapping_add i 1#usize)
           ok (cont i3)
  else ok (done (some (core.result.Result.Ok ())))

/-- [aspis_r1_cost_probe::verifier::validate_checkpoint_queries]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 354:4-360:1 -/
@[rust_loop]
def validate_loop
  (queries : Array Std.U32 22#usize) (i : Std.Usize) :
  Result (Option (core.result.Result Unit verifier.Error))
  := do
  loop
    (fun i1 => validate_loop.body queries i1)
    i

/-- [aspis_r1_cost_probe::verifier::validate_checkpoint_queries]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 352:0-360:1 -/
def validate
  (queries : Array Std.U32 22#usize) :
  Result (core.result.Result Unit verifier.Error)
  := do
  let pending_return ←
    validate_loop queries 0#usize
  match pending_return with
  | none => ok (core.result.Result.Err verifier.Error.Checkpoint)
  | some r => ok r


theorem contains (s : Slice U32) (q : U32) :
    core.slice.Slice.contains core.cmp.PartialEqU32 s q=ok (decide (q∈s.val)) := by
  unfold core.slice.Slice.contains
  induction s.val with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.anyM,core.cmp.PartialEqU32,lift,bind_tc_ok]
    by_cases same : q=x
    · subst x; simp; rfl
    · simpa [same] using ih

#print axioms contains
end AspisR1.Port5Q2_ReaderValidate
end
