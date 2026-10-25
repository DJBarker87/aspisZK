import T2Nat_RawBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_RawJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev Unwrap := OraclePortCkptAbiReadSequence.Unwrap

theorem checked_add (x y : Usize) (bound : x.val+y.val ≤ Usize.max) :
    (x+y : Result Usize) = ok (Usize.wrapping_add x y) := by
  obtain ⟨out,add,value⟩ := R22Stage2ControlBounds.add_total x y bound
  have less : x.val+y.val < UScalar.size .Usize := by
    simpa only [← value,UScalar.size] using out.hBounds
  have wrap : (Usize.wrapping_add x y).val = x.val+y.val := by
    rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt less]
  have same : out = Usize.wrapping_add x y := UScalar.eq_of_val_eq (value.trans wrap.symm)
  exact add.trans (congrArg Result.ok same)

theorem normalization (N : Usize) (unwrap : Unwrap) (r : verifier.Reader)
    (bound : r.at.val+N.val ≤ Usize.max) :
    Port5Q2_ReaderRaw.raw N (unwrap N) r = verifier.Reader.rawWithUnwrap N (unwrap N) r := by
  unfold Port5Q2_ReaderRaw.raw verifier.Reader.rawWithUnwrap
  rw [checked_add r.at N bound]
  rfl

/-- No artificial 4096-byte restriction. Any in-bounds raw call is independent
of the panic handler, with exactly the same bytes and cursor. -/
theorem reference (N : Usize) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b) = ok b) (r : verifier.Reader)
    (bound : r.at.val+N.val ≤ r.bytes.val.length) :
    Port5Q2_ReaderRaw.raw N (unwrap N) r = CheckpointBytes3Reader.raw N r := by
  rw [normalization N unwrap r (bound.trans r.bytes.property)]
  obtain ⟨b,out,run,bytes,cursor,backing⟩ :=
    OraclePortCkptAbiReader.raw_total_exact r N (unwrap N) (unwrap_ok N) bound
  obtain ⟨b1,out1,run1,bytes1,cursor1,backing1⟩ :=
    OraclePortCkptAbi2Unwrap.raw_panic_unreachable r N (fun _ => fail .panic) bound
  have bb : b=b1 := Subtype.ext (bytes.trans bytes1.symm)
  have oo : out=out1 := by
    cases out; cases out1
    simp only [verifier.Reader.mk.injEq]
    exact ⟨backing.trans backing1.symm,UScalar.eq_of_val_eq (cursor.trans cursor1.symm)⟩
  change _ = verifier.Reader.rawWithUnwrap N _ r
  rw [run,run1,bb,oo]

/-- Both directions derive their range admission from that actual call.
The result includes the physical array and mutable-reader return. -/
theorem success_iff (N : Usize) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b) = ok b)
    (r : verifier.Reader) (out : Array U8 N × verifier.Reader) :
    Port5Q2_ReaderRaw.raw N (unwrap N) r = ok out ↔
      CheckpointBytes3Reader.raw N r = ok out := by
  constructor
  · intro actual
    have bound := T2Nat_RawBounds.current_success N r (unwrap N) out actual
    rwa [reference N unwrap unwrap_ok r bound] at actual
  · intro actual
    have bound := T2Nat_RawBounds.checked_success N r _ out actual
    rwa [reference N unwrap unwrap_ok r bound]

#print axioms checked_add
#print axioms normalization
#print axioms reference
#print axioms success_iff
end AspisR1.T2Nat_RawJoin
end
