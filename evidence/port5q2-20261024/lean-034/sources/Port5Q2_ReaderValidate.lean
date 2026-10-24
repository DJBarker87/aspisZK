import Port5Q2_ReaderPrefix
import Port5Q2_Shift
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

/-- One CURRENT validator iteration reads exactly the physical prefix; the
only shift is the literal18, rebased to the installed Std U32 shift signature. -/
theorem iteration (q : Array U32 22#usize) (i : Usize)
    (pre tail : List U32) (x : U32)
    (shape : q.val=pre++x::tail) (index : i.val=pre.length) :
    validate_loop.body q i = if x.val≥262144 ∨ x∈pre then ok (.done none)
      else ok (.cont (Usize.wrapping_add i 1#usize)) := by
  have room : i.val<q.val.length := by rw [shape,index]; simp
  obtain ⟨value,read,equal⟩ := WP.spec_imp_exists (Array.index_usize_spec q i room)
  have valueEq : value=x := by
    rw [equal]
    simp [shape,index]
  subst value
  obtain ⟨front,frontRead,contents⟩ := Port5Q2_ReaderPrefix.read q i (by omega)
  have frontEq : front.val=pre := by rw [contents,shape,index]; simp
  have active : i<Slice.len (Array.to_slice q) := by change i.val<q.val.length; exact room
  simp only [validate_loop.body,lift,bind_tc_ok,if_pos active,read,
    Port5Q2_Shift.eighteen]
  by_cases high : x.val≥262144
  · simp only [show x≥262144#u32 from high,ite_true,high,true_or]
  · simp only [show ¬x≥262144#u32 from high,ite_false,frontRead,bind_tc_ok]
    rw [contains]
    rw [frontEq]
    by_cases duplicate : x∈pre <;> simp [high,duplicate]

#print axioms contains
#print axioms iteration
end AspisR1.Port5Q2_ReaderValidate
end
