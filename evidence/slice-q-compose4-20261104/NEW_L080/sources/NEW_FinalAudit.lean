import NEW_GeometryComplete
import NEW_InverseComplete
import NEW_GeometryReverse
set_option autoImplicit false
namespace NEW_FinalAudit
open Aeneas Aeneas.Std Result ControlFlow AspisR1

def zeroStep (state : core.slice.iter.Iter U32 × Unit) :
    Result (ControlFlow (core.slice.iter.Iter U32 × Unit) (Bool × core.slice.iter.Iter U32)) := do
  let (next,it) ← core.slice.iter.IteratorSliceIter.next state.1
  match next with
  | none => ok (done (false,it))
  | some value =>
    if decide (value=0#u32) then ok (done (true,it)) else ok (cont (it,()))

/-- The actual emitted zero callback has no arithmetic/domain/effect premise. -/
theorem zero_callback (x : U32) :
    NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut () x =
      ok (decide (x=0#u32),()) := by
  simp only [NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut,
    NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    NEW_GeometryActual.aspis_core.field.M31.ZERO,bind_tc_ok]

/-- One native iterator/callback observation is associated with this exact
cohort loop body. The primitive is the SAME slice iterator, not a free reply. -/
theorem zero_body (state : core.slice.iter.Iter U32 × Unit) :
    Port3_BatchStd.anyBody (core.iter.traits.iterator.IteratorSliceIter U32)
      NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
      state = zeroStep state := by
  rcases state with ⟨it,u⟩
  cases u
  simp only [Port3_BatchStd.anyBody,zeroStep,
    core.iter.traits.iterator.IteratorSliceIter,
    NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool,
    zero_callback,bind_tc_ok,uncurry]

/-- Whole partial Result transport reuses the identical body in the coherent
least-fixpoint loop. This does not unfold a buffer or assume termination. -/
theorem zero_loop (it : core.slice.iter.Iter U32) :
    Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter U32)
      NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool it () =
      loop zeroStep (it,()) := by
  unfold Port3_BatchStd.anyDefault
  have same := funext zero_body
  rw [same]

theorem native_cursor_cover (n k : Nat) (size : n=10 ∨ n=12) (active : k<n) :
    k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 := by omega

theorem native_half_cover (n k : Nat) : k<n/2 ∨ n/2≤k := by omega

theorem zero_witness_cover (row : Fin 5 → U32) :
    (∀ j, row j≠0#u32) ∨ ∃ j, row j=0#u32 := by
  classical
  by_cases h : ∀ j, row j≠0#u32
  · exact Or.inl h
  · exact Or.inr (Classical.byContradiction (fun hn => h (fun j hz => hn ⟨j,hz⟩)))

/-- Pure iterator/callback execution carries the separate caller state intact.
Native frame observations and the pinned source establish the same separation. -/
theorem zero_loop_frame {State : Type} (it : core.slice.iter.Iter U32) (state : State) :
    (Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter U32)
      NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool it (),state) =
    (loop zeroStep (it,()),state) := by rw [zero_loop]

#print axioms zeroStep
#print axioms zero_callback
#print axioms zero_body
#print axioms zero_loop
#print axioms zero_loop_frame
#print axioms native_cursor_cover
#print axioms native_half_cover
#print axioms zero_witness_cover
#print axioms NEW_GeometryComplete.complete_raw
#print axioms NEW_GeometryComplete.complete
#print axioms NEW_GeometryComplete.result_state
#print axioms NEW_GeometryComplete.accepted
#print axioms NEW_InverseComplete.result_state_effects
#print axioms NEW_GeometryReverse.state
end NEW_FinalAudit
