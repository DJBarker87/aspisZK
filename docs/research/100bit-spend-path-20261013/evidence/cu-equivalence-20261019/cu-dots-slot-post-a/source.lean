import CuSavingsDotsSlot
import CuSavingsLoopRelation

/-! Postconditions of the complete source-linked slot execution. The final
capture is immutable whenever the callback succeeds; no success is assumed.
The traversal lists the actual binds and does not use unbounded proof search. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsDotsSlotPost
open Aeneas Aeneas.Std Result AspisR1CuDots
open CuSavingsLoopRelation
variable [Arithmetic]

theorem run_post {A : Type} (bytes : Slice U8)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (k : field.wide_exact.WideExact → Result A) (P : A → Prop)
    (hk : ∀ value, All (k value) P) :
    All (CuSavingsDotsSlot.run bytes gamma slot k) P := by
  unfold CuSavingsDotsSlot.run
  apply all_bind
  intro value1
  apply all_bind
  intro value2
  apply all_bind
  intro value3
  apply all_bind
  intro value4
  apply all_bind
  intro value5
  apply all_bind
  intro value6
  apply all_bind
  intro value7
  apply all_bind
  intro value8
  apply all_bind
  intro value9
  apply all_bind
  intro value10
  apply all_bind
  intro value11
  apply all_bind
  intro value12
  apply all_bind
  intro value13
  apply all_bind
  intro value14
  rcases value14 with ⟨r,tail1⟩
  change All (do
      core.result.Result.unwrap core.fmt.DebugUnit r
      let tail2 ← old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
        {start := 0#usize,«end» := 2#usize} bytes gamma slot tail1
      let we1 ← fast_pairing.EbyKDot.finish tail2
      let we2 ← field.wide_exact.WideExact.add value5 we1
      k we2) P
  apply all_bind
  intro value15
  apply all_bind
  intro value16
  apply all_bind
  intro value17
  apply all_bind
  intro value18
  exact hk value18

theorem source_capture (state : old_dots.four_dots.closure) (slot : Usize) :
    All (old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      state slot) (fun result => result.2 = state) := by
  rcases state with ⟨bytes,gamma⟩
  rw [CuSavingsDotsSlot.old_factor]
  apply run_post
  intro value
  apply all_ok
  rfl

#print axioms run_post
#print axioms source_capture
end AspisR1.CuSavingsDotsSlotPost
