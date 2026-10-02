import AspisV8R19.R198CurrentBytesBodyMap
import AspisV8R19.R199FiniteLoopMap
import AspisV8R19.R200CurrentBytesRank

/-! Complete current serializer correspondence. This reuses the completed
generic serializer after proving the selected current body and finite loop map. -/
set_option autoImplicit false
namespace AspisV8R19.R201CurrentBytesExecution
open Aeneas Aeneas.Std Result ControlFlow
open AspisR156FullFreeze.aspis_core
open R198CurrentBytesBodyMap

def stateMap (st : CurrentIter × alloc.vec.Vec U8) :
    ScheduleIter × alloc.vec.Vec U8 := (mapIter st.1, st.2)

theorem loop_refinement (iter : CurrentIter) (b : alloc.vec.Vec U8) :
    AspisR197CurrentBytes.bytes_loop iter b =
      AspisR151QuerySchedule.bytes_loop (mapIter iter) b := by
  have hcf : R199FiniteLoopMap.mapControl stateMap = mapCF := by
    funext cf
    cases cf with
    | done b => rfl
    | cont st => rcases st with ⟨it,buf⟩; rfl
  have hstep : ∀ st : CurrentIter × alloc.vec.Vec U8,
      (do let cf ← AspisR197CurrentBytes.bytes_loop.body st.1 st.2
          ok (R199FiniteLoopMap.mapControl stateMap cf)) =
        AspisR151QuerySchedule.bytes_loop.body (stateMap st).1 (stateMap st).2 := by
    intro st
    rw [hcf]
    exact body_map st.1 st.2
  have hdecr : ∀ st next : CurrentIter × alloc.vec.Vec U8,
      AspisR197CurrentBytes.bytes_loop.body st.1 st.2 = .ok (.cont next) →
        R200CurrentBytesRank.rank next < R200CurrentBytesRank.rank st := by
    rintro ⟨it,buf⟩ ⟨it1,buf1⟩ h
    exact R200CurrentBytesRank.body_continuation_rank it buf it1 buf1 h
  simpa only [AspisR197CurrentBytes.bytes_loop,
    AspisR151QuerySchedule.bytes_loop, stateMap] using
    R199FiniteLoopMap.loop_map
      (fun st => AspisR197CurrentBytes.bytes_loop.body st.1 st.2)
      (fun st => AspisR151QuerySchedule.bytes_loop.body st.1 st.2)
      stateMap R200CurrentBytesRank.rank hstep hdecr (iter,b)

theorem bytes_refinement (v : Slice field.QM31) :
    AspisR197CurrentBytes.bytes v =
      AspisR151QuerySchedule.bytes (mapSlice v) := by
  have hlen : Slice.len (mapSlice v) = Slice.len v := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len_val, mapSlice]
  unfold AspisR197CurrentBytes.bytes AspisR151QuerySchedule.bytes
  rw [hlen]
  simp only [lift, bind_tc_ok, core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok]
  congr 1
  funext buf
  rw [loop_refinement]
  rfl

theorem bytes_execution (v : Slice field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max) :
    AspisR197CurrentBytes.bytes v =
      .ok (R144BeforeOodBytesBridge.encoded (mapSlice v)
        (by simpa only [mapSlice, List.length_map] using hsize)) := by
  rw [bytes_refinement]
  exact R153ScheduleBytesBridge.bytes_execution (mapSlice v) _

#print axioms loop_refinement
#print axioms bytes_refinement
#print axioms bytes_execution
end AspisV8R19.R201CurrentBytesExecution
