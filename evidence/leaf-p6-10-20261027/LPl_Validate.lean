import LPl_Scan
import LPl_G_Validation
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPl.Validate

def predicate (bs : List U8) (i : Nat) : Bool :=
  LPl.Echeck.chunk ((bs.drop (32*i)).take 32) true

theorem bad_eq (bs : List U8) : (fun i => !predicate bs i) = LPl_A.Validate.bad bs := by
  funext i; simp only [predicate,LPl.Echeck.chunk_eq,LPl_A.Validate.bad]

theorem window (bs : List U8) (i : Nat) (w : LPl.Scan.Window bs 32 i) :
    LPl.Echeck.chunk w.bytes true = !LPl_A.Validate.bad bs i := by
  rw [LPl.Scan.window_eq bs 32 i w (fun b => LPl.Echeck.chunk b true),LPl.Echeck.chunk_eq]
  simp only [LPl_A.Validate.bad,Bool.not_not]

theorem first_error (bs : List U8) (out : Option Nat)
    (trace : LPl.Scan.Trace (predicate bs) (bs.length/32) 0 out) :
    out = LPl_A.Validate.loop bs := by
  rw [LPl.Scan.first_error _ _ _ trace,bad_eq]; rfl

/-- Full source Result with the SAME row and the exact first-error index;
    the native usize port is value-preserving on all reached indices. -/
theorem native_result (row : U8) (bs : Slice U8) (out : Option Nat)
    (size : bs.val.length ≤ 3712)
    (trace : LPl.Scan.Trace (predicate bs.val) (bs.val.length/32) 0 out) :
    r1_wire.validate_record_fields row bs =
      match out with
      | none => ok (.Ok ())
      | some i => if h : i ≤ UScalar.cMax .Usize then
          ok (.Err (.NonCanonical row (UScalar.ofNat i h))) else fail .panic := by
  rw [LPl_A.Validate.shipped_leaf_model,← first_error bs.val out trace]
  cases out <;> rfl

/-- The index/error branch never overflows the cohort's scalar port. -/
theorem error_bound (bs : Slice U8) (i : Nat) (size : bs.val.length ≤ 3712)
    (trace : LPl.Scan.Trace (predicate bs.val) (bs.val.length/32) 0 (some i)) :
    i < 116 ∧ i ≤ UScalar.cMax .Usize := by
  have h := first_error bs.val (some i) trace
  have bound := LPl_A.firstBad_bound (LPl_A.Validate.bad bs.val) (bs.val.length/32) i h.symm
  exact ⟨by omega,LPl_A.Validate.error_index_bound bs size i h.symm⟩

/-- Uses the inherited first-error preservation law on the same source bytes. -/
theorem earlier_error (row : U8) (bs : Slice U8) (size : bs.val.length=3712)
    (n i : Nat) (bound : n≤116)
    (hit : LPl_A.firstBad (LPl_A.Validate.bad bs.val) n=some i) :
    ∃ h : i ≤ UScalar.cMax .Usize,
      r1_wire.validate_record_fields row bs = ok (.Err (.NonCanonical row (UScalar.ofNat i h))) :=
  LPl_G.validation_error row bs size n i bound hit

theorem unique (bs : List U8) (a b : Option Nat)
    (left : LPl.Scan.Trace (predicate bs) (bs.length/32) 0 a)
    (right : LPl.Scan.Trace (predicate bs) (bs.length/32) 0 b) : a=b :=
  LPl.Scan.unique _ _ _ _ _ left right

theorem total (bs : List U8) : ∃ out, LPl.Scan.Trace (predicate bs) (bs.length/32) 0 out :=
  LPl.Scan.exists_trace (predicate bs) (bs.length/32) 0 (bs.length/32) (by omega) (by omega)

#print axioms bad_eq
#print axioms window
#print axioms first_error
#print axioms native_result
#print axioms error_bound
#print axioms earlier_error
#print axioms unique
#print axioms total
end LPl.Validate
