import OraclePortCkptAbiReader

/-! Generic total immutable cursor simulation. It supplies exact byte blocks
for the saved-ten field schedule, without evaluating concrete checkpoint bytes.
Decoders, allocation and concrete unwrap adoption remain separate. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.OraclePortCkptAbiReadSequence
open AspisR1Stage2 OraclePortCkptAbiReader

abbrev Unwrap := (N : Usize) →
  core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N)

def width : List Usize → Nat
  | [] => 0
  | n::ns => n.val + width ns

def blocks (bytes : List U8) (at1 : Nat) : List Usize → List (List U8)
  | [] => []
  | n::ns => (bytes.drop at1).take n.val :: blocks bytes (at1+n.val) ns

def readMany (unwrap : Unwrap) (r : verifier.Reader) : List Usize →
    Result (List (List U8) × verifier.Reader)
  | [] => ok ([],r)
  | n::ns => do
    let (b,r1) ← verifier.Reader.rawWithUnwrap n (unwrap n) r
    let (rest,r2) ← readMany unwrap r1 ns
    ok (b.val::rest,r2)

theorem readMany_total (unwrap : Unwrap)
    (unwrap_ok : ∀ n b, unwrap n (.Ok b) = ok b)
    (r : verifier.Reader) (ns : List Usize)
    (bounds : r.at.val + width ns ≤ r.bytes.val.length) :
    ∃ out, readMany unwrap r ns = ok (blocks r.bytes.val r.at.val ns,out) ∧
      out.at.val = r.at.val + width ns ∧ out.bytes = r.bytes := by
  induction ns generalizing r with
  | nil => exact ⟨r,rfl,by simp only [width,Nat.add_zero],rfl⟩
  | cons n ns ih =>
    change r.at.val + (n.val + width ns) ≤ r.bytes.val.length at bounds
    obtain ⟨b,r1,hr,bytes,cursor,backing⟩ := raw_total_exact r n (unwrap n)
      (unwrap_ok n) (by omega)
    obtain ⟨out,tail,last,unchanged⟩ := ih r1 (by rw [backing,cursor]; omega)
    refine ⟨out,?_,?_,unchanged.trans backing⟩
    · rw [readMany,hr]
      change (do
        let (rest,r2) ← readMany unwrap r1 ns
        ok (b.val::rest,r2)) = _
      rw [tail]
      change ok (b.val::blocks r1.bytes.val r1.at.val ns,out) = _
      rw [bytes,backing,cursor]
      rfl
    · change out.at.val = r.at.val + (n.val + width ns)
      omega

/-- Field widths after the three digest fields and before the checksum.
Seven 32-byte values are state, two roots and four wide challenges. -/
def savedTenWidths : List Usize :=
  List.replicate 7 32#usize ++ [16#usize] ++ List.replicate 22 4#usize ++
  List.replicate 14 16#usize ++ List.replicate 2 32#usize ++ [16#usize] ++
  List.replicate 64 16#usize

theorem width_append (xs ys : List Usize) : width (xs++ys) = width xs + width ys := by
  induction xs with
  | nil => simp only [List.nil_append,width,Nat.zero_add]
  | cons n ns ih => simp only [List.cons_append,width,ih]; omega

theorem width_replicate (n : Nat) (w : Usize) : width (List.replicate n w) = n*w.val := by
  induction n with
  | zero => simp only [List.replicate_zero,width,Nat.zero_mul]
  | succ n ih => simp only [List.replicate_succ,width,ih,Nat.succ_mul]; omega

theorem savedTen_width : width savedTenWidths = 1656 := by
  simp only [savedTenWidths,width_append,width_replicate,width]
  rfl

/-- Every raw read in the complete fixed field schedule is checked-safe,
returns its exact slice from the original checkpoint, and ends at byte 1736.
No canonical-field, success, distinct-query or acceptance premise is needed. -/
theorem savedTen_reads_total (unwrap : Unwrap)
    (unwrap_ok : ∀ n b, unwrap n (.Ok b) = ok b)
    (ck : Slice U8) (length : ck.val.length = 1768) :
    ∃ out, readMany unwrap ⟨ck,80#usize⟩ savedTenWidths =
      ok (blocks ck.val 80 savedTenWidths,out) ∧
      out.at.val = 1736 ∧ out.bytes = ck := by
  obtain ⟨out,h,cursor,backing⟩ := readMany_total unwrap unwrap_ok ⟨ck,80#usize⟩
    savedTenWidths (by rw [savedTen_width]; change 80+1656 ≤ ck.val.length; omega)
  refine ⟨out,h,?_,backing⟩
  rw [savedTen_width] at cursor
  exact cursor

#print axioms readMany_total
#print axioms width_append
#print axioms width_replicate
#print axioms savedTen_width
#print axioms savedTen_reads_total
end AspisR1.OraclePortCkptAbiReadSequence
