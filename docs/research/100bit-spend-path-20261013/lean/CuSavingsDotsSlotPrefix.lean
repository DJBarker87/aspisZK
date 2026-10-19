import CuSavingsDotsSlot
import CuSavingsDotsBatches
import CuSavingsDotsTail

/-! The complete source-linked slot computation observes only the first 608
query bytes. Actual base, batch and tail loops discharge the read bounds;
the final continuation and shared arithmetic are arbitrary. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsDotsSlotPrefix
open Aeneas Aeneas.Std Result AspisR1CuDots
open CuSavingsPrefix
variable [Arithmetic]

theorem source_eq {A : Type} (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (hs : slot.val < 4) (k : field.wide_exact.WideExact → Result A) :
    CuSavingsDotsSlot.run (prefixArray bytes h).to_slice gamma slot k =
      CuSavingsDotsSlot.run bytes gamma slot k := by
  have ht : ∀ tail : fast_pairing.EbyKDot,
      old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
          {start := 0#usize,«end» := 2#usize} (prefixArray bytes h).to_slice gamma slot tail =
        old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
          {start := 0#usize,«end» := 2#usize} bytes gamma slot tail := by
    intro tail
    exact CuSavingsDotsTail.source_eq bytes h gamma slot _ tail hs (by scalar_tac)
  unfold CuSavingsDotsSlot.run
  simp only [ht]
  apply (bind_eq_iff _ _ _).mpr
  intro iter hiter
  rw [CuSavingsDotsBatches.source_eq bytes h gamma slot iter (Array.repeat 8#usize 0#u64) hs]
  apply (bind_eq_iff _ _ _).mpr
  intro limbs hlimbs
  apply (bind_eq_iff _ _ _).mpr
  intro decoded hdecoded
  apply (bind_eq_iff _ _ _).mpr
  intro valueOption hvalueOption
  apply (bind_eq_iff _ _ _).mpr
  intro value hvalue
  apply (bind_eq_iff _ _ _).mpr
  intro tail htail
  apply (bind_eq_iff _ _ _).mpr
  intro coefficient hcoefficient
  exact CuSavingsDotsReads.middle_cont bytes h slot hs _

#print axioms source_eq
end AspisR1.CuSavingsDotsSlotPrefix
