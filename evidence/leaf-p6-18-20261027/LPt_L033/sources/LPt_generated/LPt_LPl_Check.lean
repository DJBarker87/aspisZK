import LPt_LPl_Scan
open Aeneas Aeneas.Std Result LPt_LPl_Kit_Release
set_option autoImplicit false
namespace LPt_LPl.Check

def chunk (bs : List U8) : Bool :=
  (List.range 4).all fun j => decide (LPt_LPl.Echeck.word ((bs.drop (4*j)).take 4) < 2147483647)

theorem chunk_eq (bs : List U8) : chunk bs = LPt_LPl_Kit_Bytes.validChunk 4 false bs := by
  simp only [chunk,LPt_LPl_Kit_Bytes.validChunk,LPt_LPl.Echeck.word_eq_le32,Bool.not_false,Bool.true_or,Bool.and_true]

def predicate (bs : List U8) (i : Nat) : Bool := chunk ((bs.drop (16*i)).take 16)

theorem window (bs : List U8) (i : Nat) (w : LPt_LPl.Scan.Window bs 16 i) :
    chunk w.bytes = LPt_LPl_A.Check.predicate bs i := by
  rw [LPt_LPl.Scan.window_eq bs 16 i w chunk,chunk_eq]
  rfl

theorem stage (bs : List U8) (i : Nat) : predicate bs i = LPt_LPl_A.Check.predicate bs i := by
  rw [predicate,chunk_eq]; rfl

/-- SAME native iterator windows and decoder observations construct this trace;
    result is a local first-error index, not a supplied model output. -/
theorem native_result (bs : Slice U8) (out : Option Nat)
    (trace : LPt_LPl.Scan.Trace (predicate bs.val) (bs.val.length/16) 0 out) :
    LPt_External.compact.check_values bs = ok (if out.isNone then .Ok () else .Err .NonCanonical) := by
  have h := LPt_LPl.Scan.first_error _ _ _ trace
  have all := LPt_LPl.Scan.bool_none (predicate bs.val) (bs.val.length/16)
  rw [← h] at all
  rw [LPt_LPl_A.Check.shipped_leaf_model]
  have loop : LPt_LPl_A.Check.loop bs.val = out.isNone := by
    rw [← all]
    unfold LPt_LPl_A.Check.loop
    apply LPt_LPl_A.stages_congr
    intro good i hi
    rw [stage]
  rw [loop]

theorem unique (bs : List U8) (a b : Option Nat)
    (left : LPt_LPl.Scan.Trace (predicate bs) (bs.length/16) 0 a)
    (right : LPt_LPl.Scan.Trace (predicate bs) (bs.length/16) 0 b) : a=b :=
  LPt_LPl.Scan.unique _ _ _ _ _ left right

theorem total (bs : List U8) :
    ∃ out, LPt_LPl.Scan.Trace (predicate bs) (bs.length/16) 0 out :=
  LPt_LPl.Scan.exists_trace (predicate bs) (bs.length/16) 0 (bs.length/16) (by omega) (by omega)

theorem zero_chunk : chunk (List.replicate 16 (0#u8)) = true := by decide

theorem rejected_chunk : chunk ([255#u8,255#u8,255#u8,127#u8] ++
    List.replicate 12 (0#u8)) = false := by decide

#print axioms chunk_eq
#print axioms window
#print axioms stage
#print axioms native_result
#print axioms unique
#print axioms total
#print axioms zero_chunk
#print axioms rejected_chunk
end LPt_LPl.Check
