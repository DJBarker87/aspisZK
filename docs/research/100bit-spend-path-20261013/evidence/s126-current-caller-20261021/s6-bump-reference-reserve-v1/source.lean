import S6BumpReferenceExactV1
set_option autoImplicit false
namespace AspisS6BumpReferenceReserve
open Aeneas Aeneas.Std Result

abbrev WordRequest := Usize × Usize

def natural (requests : List WordRequest) : List AspisS6AlignedAllocationRange.Request :=
  requests.map (fun request => ⟨request.1.val,request.2.val⟩)

/-- Finite sequence of the SAME emitted owned Rust step, not an opaque
allocation callback. Cursor has already been initialized to an arena offset;
length0 prevents a consumed cursor from acquiring a fresh budget. -/
def reserve (cursor : Usize) : List WordRequest → Result (Option Usize)
  | [] => ok (some cursor)
  | request::rest => do
    let next ← AspisS6BumpOwnedReference.step cursor 0#usize request.1 request.2
    match next with
    | none => ok none
    | some next => reserve next rest

/-- TOTAL complete-result composition, including the exact first rejection.
Only nonzero alignments are required; insufficient capacity is a normal None,
not an assumed successful run or an unrepresented arithmetic failure. -/
theorem reserve_total_exact (requests : List WordRequest) (cursor : Usize)
    (positive : ∀ request ∈ requests, 0 < request.2.val) :
    ∃ out, reserve cursor requests = ok out ∧
      out.map UScalar.val = AspisS6AlignedAllocationRange.reserve cursor.val (natural requests) := by
  induction requests generalizing cursor with
  | nil => exact ⟨some cursor,rfl,rfl⟩
  | cons request rest ih =>
    have current := positive request (by simp)
    have tailPositive : ∀ r ∈ rest, 0 < r.2.val := by
      intro r member
      exact positive r (by simp [member])
    obtain ⟨out,called,meaning⟩ :=
      AspisS6BumpReferenceExact.step_total_exact cursor 0#usize request.1 request.2 current
    have selected : (if cursor = 0#usize then (0#usize).val else cursor.val) = cursor.val := by
      by_cases zero : cursor = 0#usize
      · subst cursor; rfl
      · simp only [zero,if_false]
    rw [selected] at meaning
    cases out with
    | none =>
      refine ⟨none,?_,?_⟩
      · simp only [reserve,called,bind_tc_ok]
      · simp only [Option.map_none] at meaning
        simp only [natural,List.map_cons,AspisS6AlignedAllocationRange.reserve,
          ← meaning,Option.bind_none,Option.map_none]
    | some middle =>
      obtain ⟨out,tailCalled,tailMeaning⟩ := ih middle tailPositive
      refine ⟨out,?_,?_⟩
      · simp only [reserve,called,bind_tc_ok,tailCalled]
      · simp only [Option.map_some] at meaning
        simpa only [natural,List.map_cons,AspisS6AlignedAllocationRange.reserve,
          ← meaning,Option.bind_some] using tailMeaning

/-- The earlier range/totality induction is now consumed by the COMPLETE
emitted owned reference sequence on bounded native word carriers. No child
success, per-step arithmetic totality or reference/model equality is input. -/
theorem reserve_fits (requests : List WordRequest) (cursor : Usize)
    (valid : ∀ request ∈ requests, 0 < request.2.val ∧ request.2.val ≤ 8)
    (fits : 8+AspisS6AlignedAllocationRange.charge (natural requests) ≤ cursor.val) :
    ∃ next, reserve cursor requests = ok (some next) ∧
      8 ≤ next.val ∧ next.val ≤ cursor.val ∧
      cursor.val ≤ next.val+AspisS6AlignedAllocationRange.charge (natural requests) := by
  have positive : ∀ request ∈ requests, 0 < request.2.val := by
    intro request member
    exact (valid request member).1
  have naturalValid : ∀ request ∈ natural requests, AspisS6AlignedAllocationRange.Valid request := by
    intro request member
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp member
    exact valid original member
  obtain ⟨n,called,header,decreasing,loss⟩ :=
    AspisS6AlignedAllocationRange.reserve_fits (natural requests) cursor.val naturalValid fits
  obtain ⟨out,source,meaning⟩ := reserve_total_exact requests cursor positive
  rw [called] at meaning
  cases out with
  | none => simp only [Option.map_none] at meaning; contradiction
  | some next =>
    have value : next.val = n := Option.some.inj meaning
    exact ⟨next,source,by omega,by omega,by omega⟩

#print axioms reserve_total_exact
#print axioms reserve_fits
end AspisS6BumpReferenceReserve
