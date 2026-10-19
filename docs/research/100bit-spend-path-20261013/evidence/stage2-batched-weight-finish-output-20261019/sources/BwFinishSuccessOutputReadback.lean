import AspisR1BatchedWeightsFinishExtraction.BatchedWeightsFinishGenerated
import BwFinishLoopSuccessValueLaw
import BwFinishSuccessValueComponents
import BwFinishValueEntryBridge
import BwFinishV20Components
import BwPrefixWriteIndex
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1BatchedWeightsFinishExtraction
namespace batched_weights
namespace FinishSuccessOutputReadback

abbrev FinishIter := core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut aspis_core.field.QM31)

theorem finish_success_output_components
    (self : BatchedWeights) (weights result : FinishSlice)
    (i : Std.Usize) (hi : i.val < weights.len.val)
    (hfinish : BatchedWeights.finish self weights = .ok result) :
    ∃ w, Slice.index_usize result i = .ok w ∧
      Nonempty (HasCanonicalValueComponents self.raw self.terms i w) := by
  obtain ⟨output, hloop, _hresult⟩ :=
    FinishSuccessValueComponents.finish_success_exposes_loop self weights result hfinish
  let initial : FinishIter := ⟨{ slice := weights }, 0#usize⟩
  have hall : ∀ j : Std.Usize, j.val < weights.len.val →
      ∃ w, BatchedWeights.value self j = .ok w := by
    intro j hj
    exact LoopSuccessValueLaw.loop_success_forces_values self weights.len.val weights.property
      initial (fun e => e) output (by simp [initial]) (by simp [initial]) hloop
      j (by simp [initial]) hj
  let toUsize : (n : Nat) → n < weights.len.val → Std.Usize := fun n hn =>
    UScalar.ofNatCore n (by have := hn; have hlen := weights.property; scalar_tac)
  let f : Nat → AspisR1BatchedWeightsExtraction.aspis_core.field.QM31 := fun n =>
    if hn : n < weights.len.val then
      Classical.choose (hall (toUsize n hn) (by
        have hval : (toUsize n hn).val = n := by
          simp [toUsize, UScalar.ofNatCore_val_eq]
        simpa [hval] using hn))
    else { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }
  have hvalue : ∀ j : Std.Usize, j.val < weights.len.val →
      BatchedWeights.value self j = .ok (f j.val) := by
    intro j hj
    have hidx : toUsize j.val hj = j := by
      apply UScalar.eq_of_val_eq
      simp [toUsize, UScalar.ofNatCore_val_eq]
    have hspec := Classical.choose_spec
      (hall (toUsize j.val hj) (by
        have hval : (toUsize j.val hj).val = j.val := by
          simp [toUsize, UScalar.ofNatCore_val_eq]
        simpa [hval] using hj))
    dsimp [f]
    rw [dif_pos hj]
    simpa only [hidx] using hspec
  obtain ⟨result', hfinish', hprefix⟩ := finish_output_invariant self weights f hvalue
  have hresultEq : result' = result := Result.ok.inj (hfinish'.symm.trans hfinish)
  have hread : Slice.index_usize result' i = .ok (f i.val) := by
    rw [hprefix]
    exact BwPrefixWriteIndex.prefixWrite_index f weights.len.val weights i le_rfl hi
  have hentry : AspisR1BatchedWeightsExtraction.batched_weights.value_entry
      self.raw self.terms i = .ok (f i.val) := by
    calc
      AspisR1BatchedWeightsExtraction.batched_weights.value_entry self.raw self.terms i =
          BatchedWeights.value { «raw» := self.raw, terms := self.terms } i :=
        BwFinishValueEntryBridge.value_entry_eq_finish_value self.raw self.terms i
      _ = BatchedWeights.value self i := by rfl
      _ = .ok (f i.val) := hvalue i hi
  have hcomponents : Nonempty (HasCanonicalValueComponents self.raw self.terms i (f i.val)) :=
    value_components_of_success self i (f i.val) hentry
  refine ⟨f i.val, ?_, hcomponents⟩
  simpa [hresultEq] using hread

#print axioms finish_success_output_components
end FinishSuccessOutputReadback
end batched_weights
end AspisR1BatchedWeightsFinishExtraction
