import NPH_R22QRawShift

/-! NPH_ (R22): FIo_Native.transport.Variant.row_loop.body is DIRECT (c) for every input.
transport.TAU is the constant 5-entry array [3,4,2,0,1]. Both semantics bounds-check the read
`TAU[d]`, so an iteration that the wrapping program completes has d < 5, and then the entry
read is < 16. Under exactly that condition the checked body returns ok (both checked shifts are
safe: shift amounts 2d < 10 and 2*TAU[d] ≤ 8). The `next` step and the wrapping_mul/&&&/|||
steps are not overflow-checked. When d ≥ 5 both semantics reject: the checked body may already
fail at the first shift, and the wrapping program fails at the bounds check. No caller domain
(iter.end ≤ 16) is used. Standard axioms. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22RowLoop
open Aeneas Aeneas.Std Result AspisR1.NPH_R22QRawShift

theorem tau_val : FIo_Native.transport.TAU.val = [3#usize, 4#usize, 2#usize, 0#usize, 1#usize] := by
  unfold FIo_Native.transport.TAU; rfl

/-- Every TAU entry read in bounds is below 16. -/
theorem tau_entry_lt (d t : Usize) (hlen : d.val < FIo_Native.transport.TAU.length)
    (htv : t = FIo_Native.transport.TAU.val[d.val]) : t.val < 16 := by
  have hmem : t ∈ FIo_Native.transport.TAU.val := by
    rw [htv]; first | exact List.getElem_mem _ | exact List.getElem_mem .. | simp
  rw [tau_val] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> first | decide | simp | scalar_tac

/-- DIRECT: with the TAU read in bounds (d < 5), the checked row_loop body returns ok. -/
theorem row_loop_body_ok (j : Usize) (iter iter1 : core.ops.range.Range Usize) (out d : Usize)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some d, iter1))
    (hd : d.val < 5) :
    ∃ v, FIo_Native.transport.Variant.row_loop.body j iter out = ok v := by
  have hlen : d.val < FIo_Native.transport.TAU.length := by
    have hp := FIo_Native.transport.TAU.property
    first
      | (simp only [Array.length, hp]; first | omega | scalar_tac | (simp; omega))
      | (simpa [hp] using hd)
      | scalar_tac
  obtain ⟨t, ht, htv⟩ := WP.spec_imp_exists (Array.index_usize_spec FIo_Native.transport.TAU d hlen)
  have htl := tau_entry_lt d t hlen htv
  obtain ⟨s, hs⟩ := row_shr_ok j d (by omega)
  obtain ⟨s2, hs2⟩ := row_shl_ok (s &&& 3#usize) t htl
  unfold FIo_Native.transport.Variant.row_loop.body
  simp only [hn, bind_tc_ok, lift, hs, ht, hs2]
  exact ⟨_, rfl⟩

/-- The exhausted-iterator case is ok for every input. -/
theorem row_loop_body_done (j : Usize) (iter iter1 : core.ops.range.Range Usize) (out : Usize)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (none, iter1)) :
    FIo_Native.transport.Variant.row_loop.body j iter out = ok (ControlFlow.done out) := by
  unfold FIo_Native.transport.Variant.row_loop.body
  simp only [hn, bind_tc_ok]

#print axioms tau_val
#print axioms tau_entry_lt
#print axioms row_loop_body_ok
#print axioms row_loop_body_done
end AspisR1.NPH_R22RowLoop
