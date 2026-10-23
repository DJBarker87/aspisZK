import S2W_Snapshot

/-! Focused value facts about the exact native snapshot emission. Acquisition,
dereference and error-clone observations are still primitive SDK cuts; no
native instance, allocation-frame or guard-drop effect is inferred. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W.Snapshot
open Aeneas Aeneas.Std Result

/-- Symbolic std-copy identity, independent of the admitted account size. -/
theorem to_vec_identity (data : Slice U8) :
    alloc.slice.Slice.to_vec core.clone.CloneU8 data = ok data := by
  have cloned : Slice.clone core.clone.CloneU8.clone data = ok data := by
    obtain ⟨copied, call, same⟩ := WP.spec_imp_exists
      (Slice.clone_spec (s := data) (clone := core.clone.CloneU8.clone)
        (by intro _ _; rfl))
    simpa [← same] using call
  exact cloned

/-- Complete metadata projection actually copied by snapshot. Lamports and
rent_epoch are not present in OwnedAccount and are not reconstructed here. -/
def projected (C : Carriers) (account : AccountInfo C)
    (length : core.result.Result Usize PE)
    (bytes : core.result.Result (alloc.vec.Vec U8) PE) : OwnedAccount :=
  {key := account.key, owner := account.owner, is_signer := account.is_signer,
   is_writable := account.is_writable, executable := account.executable,
   length := length, bytes := bytes}

/-- Both admitted length branches return the original slice bytes and length.
No copy/length conclusion is a hypothesis. External guard observations stay
explicit until related to the SDK machine on the same native execution. -/
theorem admitted_snapshot (C : Carriers) (ops : Ops C) (account : AccountInfo C)
    (length1 length2 : Usize) (guard : C.Ref (Slice U8))
    (back : core.result.Result (C.Ref (Slice U8)) PE → Unit) (data : Slice U8)
    (borrow : ops.borrow account = ok (.Ok guard, back))
    (deref : ops.deref guard = ok data)
    (admitted : Slice.len data = length1 ∨ Slice.len data = length2) :
    snapshot C ops account length1 length2 =
      ok (projected C account (.Ok (Slice.len data)) (.Ok data)) := by
  rcases admitted with first | second
  · simp [snapshot, borrow, deref, first, to_vec_identity, projected] <;> rfl
  · by_cases first : Slice.len data = length1
    · simp [snapshot, borrow, deref, first, to_vec_identity, projected] <;> rfl
    · simp [snapshot, borrow, deref, first, second, to_vec_identity, projected] <;> rfl

/-- Malformed lengths preserve their actual length and defer InvalidAccountData;
no allocation or to_vec invocation occurs on this branch of the emission. -/
theorem rejected_length (C : Carriers) (ops : Ops C) (account : AccountInfo C)
    (length1 length2 : Usize) (guard : C.Ref (Slice U8))
    (back : core.result.Result (C.Ref (Slice U8)) PE → Unit) (data : Slice U8)
    (borrow : ops.borrow account = ok (.Ok guard, back))
    (deref : ops.deref guard = ok data)
    (first : Slice.len data ≠ length1) (second : Slice.len data ≠ length2) :
    snapshot C ops account length1 length2 =
      ok (projected C account (.Ok (Slice.len data))
        (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)) := by
  simp [snapshot, borrow, deref, first, second, projected]

/-- The error clone result is retained exactly, rather than asserting that
an opaque clone succeeds or has any particular value. -/
theorem borrow_error (C : Carriers) (ops : Ops C) (account : AccountInfo C)
    (length1 length2 : Usize) (error cloned : PE)
    (back : core.result.Result (C.Ref (Slice U8)) PE → Unit)
    (borrow : ops.borrow account = ok (.Err error, back))
    (clone : ops.cloneError error = ok cloned) :
    snapshot C ops account length1 length2 =
      ok (projected C account (.Err cloned) (.Err error)) := by
  simp [snapshot, borrow, clone, projected]

/-- Acceptance of a snapshot's data projection implies admitted length and
consistent length/bytes, without an assumed OwnedSnapshotShape or entrySize.
This statement covers the extracted snapshot only, prior to native reification. -/
theorem successful_shape (C : Carriers) (ops : Ops C) (account : AccountInfo C)
    (length1 length2 : Usize) (out : OwnedAccount) (bytes : alloc.vec.Vec U8)
    (returned : snapshot C ops account length1 length2 = ok out)
    (successful : out.bytes = .Ok bytes) :
    out.length = .Ok (alloc.vec.Vec.len bytes) ∧
    (alloc.vec.Vec.len bytes = length1 ∨ alloc.vec.Vec.len bytes = length2) := by
  unfold snapshot at returned
  cases borrowed : ops.borrow account with
  | fail error => simp [borrowed] at returned
  | div => simp [borrowed] at returned
  | ok pair =>
    rcases pair with ⟨result,back⟩
    cases result with
    | Err error =>
      cases cloned : ops.cloneError error with
      | fail e => simp [borrowed,cloned] at returned
      | div => simp [borrowed,cloned] at returned
      | ok e =>
        simp [borrowed,cloned] at returned
        subst out
        cases successful
    | Ok guard =>
      cases read : ops.deref guard with
      | fail e => simp [borrowed,read] at returned
      | div => simp [borrowed,read] at returned
      | ok data =>
        by_cases first : Slice.len data = length1
        · simp [borrowed,read,first,to_vec_identity] at returned
          have outEq : projected C account (.Ok length1) (.Ok data) = out :=
            Result.ok.inj returned
          subst out
          have same : data = bytes := core.result.Result.Ok.inj successful
          subst bytes
          exact ⟨congrArg core.result.Result.Ok first.symm, Or.inl first⟩
        · by_cases second : Slice.len data = length2
          · simp [borrowed,read,first,second,to_vec_identity] at returned
            have outEq : projected C account (.Ok length2) (.Ok data) = out :=
              Result.ok.inj returned
            subst out
            have same : data = bytes := core.result.Result.Ok.inj successful
            subst bytes
            exact ⟨congrArg core.result.Result.Ok second.symm, Or.inr second⟩
          · simp [borrowed,read,first,second] at returned
            subst out
            cases successful

/-- Exact1768-byte entry length follows from the wrapper's admitted bounds,
not an independent entrySize premise. Native output association stays open. -/
theorem checkpoint_entry_size (C : Carriers) (ops : Ops C) (account : AccountInfo C)
    (out : OwnedAccount) (bytes : alloc.vec.Vec U8)
    (returned : snapshot C ops account 1768#usize 1768#usize = ok out)
    (successful : out.bytes = .Ok bytes) : bytes.val.length = 1768 := by
  have shape := successful_shape C ops account 1768#usize 1768#usize out bytes
    returned successful
  have len : alloc.vec.Vec.len bytes = 1768#usize := shape.2.elim id id
  exact congrArg UScalar.val len

#print axioms to_vec_identity
#print axioms admitted_snapshot
#print axioms rejected_length
#print axioms borrow_error
#print axioms successful_shape
#print axioms checkpoint_entry_size
end AspisR1.S2W.Snapshot
end
