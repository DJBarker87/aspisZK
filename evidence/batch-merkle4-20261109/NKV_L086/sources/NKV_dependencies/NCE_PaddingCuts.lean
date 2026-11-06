import NBJ_PaddingPort

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_PaddingCuts
open Aeneas Aeneas.Std Result ControlFlow

abbrev Iter := core.slice.iter.ChunksExact U8
abbrev Body (Frame : Type) := (Iter × Frame) →
  Result (ControlFlow (Iter × Frame) (Bool × Iter × Frame))

/-- Exact extracted iterator/predicate iteration with an unchanged caller
frame. Neither a complete scan nor its Boolean is a parameter. -/
def body {Frame : Type} (predicate : core.ops.function.FnMut Unit (Slice U8) Bool)
    (s : Iter × Frame) : Result (ControlFlow (Iter × Frame) (Bool × Iter × Frame)) := do
  let step ← Port3_BatchStd.anyBody (core.iter.traits.iterator.IteratorChunksExact U8)
    predicate (s.1,())
  match step with
  | .cont (after,_) => ok (.cont (after,s.2))
  | .done (stop,after) => ok (.done (stop,after,s.2))

/-- Prospective ONE-iteration native cut, on an arbitrary physical iterator
prestate and arbitrary caller frame. Every reached chunk is exactly 8 bytes;
the native predicate value must be bound separately to NBJ_Padding.word_exact.
The unchanged remainder is exterior state, not a successful-scan premise. -/
def NCE_Native_Padding {Frame : Type}
    (predicate : core.ops.function.FnMut Unit (Slice U8) Bool) (native : Body Frame) : Prop :=
  ∀ (it : Iter) (frame : Frame), (∀ c ∈ it.chunks, c.val.length = 8) →
    native (it,frame) = body predicate (it,frame)

/-- Source-specific native continuation; a Kani obligation is only ONE body
iteration. The fuel is the iterator's initial number of chunks plus its final
empty test, not a bound on an adversary's global digest history. -/
def run {Frame : Type} (native : Body Frame) : Nat → Iter × Frame → Result (Bool × Iter × Frame)
  | 0,_ => .div
  | fuel+1,s => do
      let step ← native s
      match step with
      | .cont after => run native fuel after
      | .done out => ok out

/-- Complete same-carrier iterator result, including the first-stop remainder
and predicate failure/divergence. Existing NBI scan semantics are consumed;
no all-zero/final-scan success is assumed. -/
theorem run_eq {Frame : Type}
    (predicate : core.ops.function.FnMut Unit (Slice U8) Bool) (native : Body Frame)
    (cut : NCE_Native_Padding predicate native) (chunks : List (Slice U8))
    (remainder : Slice U8) (frame : Frame)
    (sizes : ∀ c ∈ chunks, c.val.length = 8) :
    run native (chunks.length+1) ({chunks:=chunks,remainder:=remainder},frame) =
      (do let (stop,after) ← NBI_Padding.scan predicate remainder chunks
          ok (stop,after,frame)) := by
  induction chunks with
  | nil =>
    rw [show ([] : List (Slice U8)).length+1 = 1 from rfl,run,cut _ frame sizes]
    simp only [body,Port4B_AnyFalse.body_nil,bind_tc_ok,NBI_Padding.scan]
    rfl
  | cons chunk rest ih =>
    rw [show (chunk::rest).length+1 = (rest.length+1)+1 by simp only [List.length_cons]]
    rw [run,cut _ frame sizes]
    simp only [body,Port4B_AnyFalse.body_cons,NBI_Padding.scan]
    generalize returned : predicate.call_mut () chunk = out
    cases out with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨stop,state⟩
      cases state
      cases stop with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true,if_false,bind_tc_ok]
        exact ih (fun c mem => sizes c (List.mem_cons_of_mem _ mem))

/-- Existing first-stop law consumes the same physical chunk prefix. The
unvisited suffix is retained; it is not replaced by an empty iterator. -/
theorem first_stop {Frame : Type}
    (predicate : core.ops.function.FnMut Unit (Slice U8) Bool) (native : Body Frame)
    (cut : NCE_Native_Padding predicate native) (front suffix : List (Slice U8))
    (chunk remainder : Slice U8) (frame : Frame)
    (sizes : ∀ c ∈ front++chunk::suffix, c.val.length = 8)
    (zero : ∀ c ∈ front, predicate.call_mut () c = ok (false,()))
    (nonzero : predicate.call_mut () chunk = ok (true,())) :
    run native ((front++chunk::suffix).length+1)
      ({chunks:=front++chunk::suffix,remainder:=remainder},frame) =
      ok (true,{chunks:=suffix,remainder:=remainder},frame) := by
  rw [run_eq predicate native cut _ remainder frame sizes,
    NBI_Padding.first_stop predicate front suffix chunk remainder zero nonzero]
  rfl

#print axioms run_eq
#print axioms first_stop
end AspisR1.NCE_PaddingCuts
end
