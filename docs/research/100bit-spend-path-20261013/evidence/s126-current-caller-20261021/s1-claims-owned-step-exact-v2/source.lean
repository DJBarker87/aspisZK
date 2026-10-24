import S1ClaimsOwnedStepFunsV1
set_option autoImplicit false
namespace AspisS1ClaimsOwnedStepExact
open Aeneas Aeneas.Std Result AspisS1ClaimsOwnedStep
abbrev Q := aspis_core.field.QM31
abbrev Row := Array Q 29#usize
abbrev Claims := Array Row 3#usize
abbrev Decoded := core.result.Result Row r1_wire.Error
abbrev Status := core.result.Result Unit r1_wire.Error

theorem error_exact (before : Claims) (p : Usize) (error : r1_wire.Error) :
    r1_semantic.claims_owned_step before p (.Err error) = ok (.Err error,before) := rfl

/-- TOTAL on the actual loop's index domain, for every full raw row/state.
No numeric canonicality, successful update or opaque state law is assumed. -/
theorem ok_exact (before : Claims) (p : Usize) (row : Row) (hp : p.val < 3) :
    r1_semantic.claims_owned_step before p (.Ok row) = ok (.Ok (),before.set p row) := by
  have h : p.val < before.val.length := by simpa [before.property] using hp
  change (do let after ← Aeneas.Std.Array.update before p row
             ok (core.result.Result.Ok (),after)) = _
  unfold Aeneas.Std.Array.update
  change (do let after ← (match before.val[p.val]? with
                 | none => fail Error.arrayOutOfBounds
                 | some _ => ok (before.set p row))
             ok (core.result.Result.Ok (),after)) = _
  rw [List.getElem?_eq_getElem h]
  rfl

/-- Composition of the actual extracted owned step. Inputs are the normally
returned decoded rows/errors, in order; native allocation/cleanup and the
complete decoder's execution are outside this reference function. -/
def run (before : Claims) : List (Usize × Decoded) → Result (Status × Claims)
  | [] => ok (.Ok (),before)
  | (p,decoded)::tail => do
    let (status,after) ← r1_semantic.claims_owned_step before p decoded
    match status with
    | .Err error => ok (.Err error,after)
    | .Ok () => run after tail

/-- Induction over the chunk count. Every bounded normally returned decode
schedule has a total owned composition, including the first error's exact
state/return. This is not whole native Claims or allocator TOTAL. -/
theorem run_total (before : Claims) (inputs : List (Usize × Decoded))
    (bounds : ∀ input ∈ inputs, input.1.val < 3) :
    ∃ status after, run before inputs = ok (status,after) := by
  induction inputs generalizing before with
  | nil => exact ⟨.Ok (),before,rfl⟩
  | cons input tail ih =>
    rcases input with ⟨p,decoded⟩
    cases decoded with
    | Err error =>
      exact ⟨.Err error,before,rfl⟩
    | Ok row =>
      have hp := bounds (p,.Ok row) (by simp)
      obtain ⟨status,after,rest⟩ := ih (before.set p row)
        (fun input member => bounds input (by simp [member]))
      refine ⟨status,after,?_⟩
      simp only [run,ok_exact before p row hp,bind_tc_ok]
      exact rest

theorem first_error_exact (before : Claims) (p : Usize) (error : r1_wire.Error)
    (tail : List (Usize × Decoded)) :
    run before ((p,.Err error)::tail) = ok (.Err error,before) := rfl

private theorem overwrite_three (before : Claims) (row0 row1 row2 : Row) :
    ((before.set 0#usize row0).set 1#usize row1).set 2#usize row2 =
      (⟨[row0,row1,row2],by simp⟩ : Claims) := by
  apply Subtype.ext
  obtain ⟨a,b,c,shape⟩ := List.length_eq_three.mp before.property
  change (((before.val.set 0 row0).set 1 row1).set 2 row2) = [row0,row1,row2]
  rw [shape]
  rfl

/-- The fixed three successful rows overwrite the entire complete carrier;
no sentinel/suffix value survives. Native initializedness and the loop-to-
reference transport remain separate from this pure owned composition. -/
theorem three_rows_exact (before : Claims) (row0 row1 row2 : Row) :
    run before [(0#usize,.Ok row0),(1#usize,.Ok row1),(2#usize,.Ok row2)] =
      ok (.Ok (), (⟨[row0,row1,row2],by simp⟩ : Claims)) := by
  rw [run,ok_exact before 0#usize row0 (by decide)]
  simp only [bind_tc_ok]
  rw [run,ok_exact _ 1#usize row1 (by decide)]
  simp only [bind_tc_ok]
  rw [run,ok_exact _ 2#usize row2 (by decide)]
  simp only [bind_tc_ok,run,overwrite_three]

#print axioms error_exact
#print axioms ok_exact
#print axioms run_total
#print axioms first_error_exact
#print axioms three_rows_exact
end AspisS1ClaimsOwnedStepExact
