import OraclePortCkptAbiReadSequence

/-! The error branch is a continuation, never a Formatter instance. Theorems
quantify over every panic implementation, including failure and divergence.
The native library/translation identification remains a source boundary. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.OraclePortCkptAbi2Unwrap
open AspisR1Stage2 OraclePortCkptAbiReadSequence

def unwrapWithPanic {A E : Type} (panic : E → Result A) :
    core.result.Result A E → Result A
  | .Ok value => ok value
  | .Err err => panic err

theorem unwrap_ok {A E : Type} (panic : E → Result A) (value : A) :
    unwrapWithPanic panic (.Ok value) = ok value := rfl

/-- Safe range conversion reaches Ok before the panic branch is selected.
Exact returned bytes and post-state hold for every possible panic handler. -/
theorem raw_panic_unreachable (r : verifier.Reader) (N : Usize)
    (panic : core.array.TryFromSliceError → Result (Array U8 N))
    (bounds : r.at.val + N.val ≤ r.bytes.val.length) :
    ∃ b out, verifier.Reader.rawWithUnwrap N (unwrapWithPanic panic) r = ok (b,out) ∧
      b.val = (r.bytes.val.drop r.at.val).take N.val ∧
      out.at.val = r.at.val + N.val ∧ out.bytes = r.bytes :=
  OraclePortCkptAbiReader.raw_total_exact r N _ (unwrap_ok panic) bounds

/-- Replacing the panic branch changes neither the bytes nor the cursor.
This proves unreachability by observational independence, with total success. -/
theorem raw_panic_independent (r : verifier.Reader) (N : Usize)
    (p q : core.array.TryFromSliceError → Result (Array U8 N))
    (bounds : r.at.val + N.val ≤ r.bytes.val.length) :
    verifier.Reader.rawWithUnwrap N (unwrapWithPanic p) r =
      verifier.Reader.rawWithUnwrap N (unwrapWithPanic q) r := by
  obtain ⟨b, s, hs, hb, ha, hx⟩ := raw_panic_unreachable r N p bounds
  obtain ⟨c, t, ht, hc, hd, hy⟩ := raw_panic_unreachable r N q bounds
  have bc : b = c := Subtype.ext (hb.trans hc.symm)
  have st : s = t := by
    cases s with | mk sb sa =>
      cases t with | mk tb ta =>
        simp only [verifier.Reader.mk.injEq]
        exact ⟨hx.trans hy.symm, by
          apply UScalar.eq_of_val_eq
          exact ha.trans hd.symm⟩
  rw [hs,ht,bc,st]

/-- All saved-ten raw reads succeed with an arbitrary panic continuation.
No caller-supplied unwrap-on-Ok contract is needed. -/
theorem savedTen_panic_unreachable
    (panic : (N : Usize) → core.array.TryFromSliceError → Result (Array U8 N))
    (ck : Slice U8) (length : ck.val.length = 1768) :
    ∃ out, readMany (fun n => unwrapWithPanic (panic n)) ⟨ck,80#usize⟩ savedTenWidths =
      ok (blocks ck.val 80 savedTenWidths,out) ∧
      out.at.val = 1736 ∧ out.bytes = ck :=
  savedTen_reads_total _ (fun n => unwrap_ok (panic n)) ck length

#print axioms unwrap_ok
#print axioms raw_panic_unreachable
#print axioms raw_panic_independent
#print axioms savedTen_panic_unreachable
end AspisR1.OraclePortCkptAbi2Unwrap
