import PV_L2C_HashLoopRange
import R1Z.PV_RunJoin_EnumerateTrace
set_option autoImplicit false
namespace PV_L2C_AbsorbRange
open Aeneas Aeneas.Std Result R1Z R0Z.WriterRefine BuilderStdModels
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep

abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32)
abbrev iterator := core.iter.traits.iterator.IteratorEnumerate
  (core.iter.traits.iterator.IteratorSliceIter U32)

/-- Totality and raw range of the actual absorb loop on a finite native
iterator trace. The trace fixes source order and the real update result. -/
theorem trace (i : Iter) (pairs : List (Usize × U32))
    (ht : FiniteTrace iterator i pairs)
    (hb : ∀ p ∈ pairs, p.1.val < 16 ∧ p.2.val < 2147483647)
    (s : State) (hc : Canonical s) :
    ∃ out, poseidon2.hash_fields_with_trace_loop0_loop0 i s = ok out ∧ Canonical out := by
  induction ht generalizing s with
  | done i j hn =>
    simp only [iterator,core.iter.traits.iterator.IteratorEnumerate] at hn
    refine ⟨s,?_,hc⟩
    rw [poseidon2.hash_fields_with_trace_loop0_loop0.eq_1,hn]
    rfl
  | step i j p ps hn tail ih =>
    simp only [iterator,core.iter.traits.iterator.IteratorEnumerate] at hn
    obtain ⟨hindex,hword⟩ := hb p (by simp)
    obtain ⟨z,hadd,_,hz⟩ := PV_Src_PortAddition.canonical
      s.val[p.1.val]! p.2 (hc ⟨p.1.val,hindex⟩) hword
    have updated := canonical_set s p.1 hindex z hz hc
    obtain ⟨out,ho,hcan⟩ := ih (fun q hq => hb q (by simp [hq])) (s.set p.1 z) updated
    refine ⟨out,?_,hcan⟩
    rw [poseidon2.hash_fields_with_trace_loop0_loop0.eq_1,hn]
    simp only [bind_tc_ok]
    rw [index_ok s p.1 (by simpa using hindex)]
    simp only [bind_tc_ok,hadd]
    rw [BuilderRecordsArray.update_gen _ p.1 z (by simpa using hindex)]
    exact ho
#print axioms trace

theorem labels_range (xs : List U32) (count : Usize)
    (hc : count.val + xs.length ≤ 16) (hx : ∀ x ∈ xs, x.val < 2147483647) :
    ∀ p ∈ PV_RunJoin_EnumerateTrace.labels count xs,
      p.1.val < 16 ∧ p.2.val < 2147483647 := by
  induction xs generalizing count with
  | nil => simp [PV_RunJoin_EnumerateTrace.labels]
  | cons x xs ih =>
    have hcount : count.val < 24 := by simp only [List.length_cons] at hc; omega
    have hn := BuilderRecordsArray.next_val count hcount
    have nextBound : (Usize.wrapping_add count 1#usize).val + xs.length ≤ 16 := by
      rw [hn];simp only [List.length_cons] at hc;omega
    intro p hp
    rcases List.mem_cons.mp hp with he | ht
    · subst p
      exact ⟨by simp only [List.length_cons] at hc;omega,hx x (by simp)⟩
    · exact ih (Usize.wrapping_add count 1#usize) nextBound
        (fun v hv => hx v (by simp [hv])) p ht
#print axioms labels_range

theorem entry (input : Slice U32) (hi : input.val.length ≤ 8)
    (hx : ∀ x ∈ input.val, x.val < 2147483647) (s : State) (hs : Canonical s) :
    ∃ out, poseidon2.hash_fields_with_trace_loop0_loop0
      ⟨⟨input,0⟩,0#usize⟩ s = ok out ∧ Canonical out := by
  have ht := PV_RunJoin_EnumerateTrace.trace
    (core.iter.traits.iterator.IteratorSliceIter U32) ⟨input,0⟩ input.val
    (by simpa using BuilderSliceCollect.slice_trace input 0) 0#usize (by simp; omega)
  exact trace _ _ ht (labels_range input.val 0#usize (by simp;omega) hx) s hs
#print axioms entry
end PV_L2C_AbsorbRange
