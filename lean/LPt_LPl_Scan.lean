import LPt_LPl_EcheckResult
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace LPt_LPl.Scan
/-- Source-order scan preserving the index of the FIRST failure. -/
def run (p : Nat → Bool) (i : Nat) : Nat → Option Nat
  | 0 => none
  | n+1 => if p i then run p (i+1) n else some i

inductive Trace (p : Nat → Bool) (count : Nat) : Nat → Option Nat → Prop where
  | done (i : Nat) (endOfIterator : i = count) : Trace p count i none
  | reject (i : Nat) (live : i < count) (bad : p i = false) : Trace p count i (some i)
  | next (i : Nat) (live : i < count) (good : p i = true)
      (out : Option Nat) (rest : Trace p count (i+1) out) : Trace p count i out

theorem result (p : Nat → Bool) (count i : Nat) (out : Option Nat)
    (h : Trace p count i out) : out = run p i (count-i) := by
  induction h with
  | done i endOfIterator => simp [endOfIterator,run]
  | reject i live bad =>
    have hn : count-i = (count-i-1)+1 := by omega
    rw [hn,run,bad]; rfl
  | next i live good out rest ih =>
    have hn : count-i = (count-(i+1))+1 := by omega
    rw [hn,run,good]
    exact ih

theorem run_find (p : Nat → Bool) (n i : Nat) :
    run p i n = (List.range' i n).find? (fun j => !p j) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [run,List.range'_succ,List.find?,Nat.add_one]; cases h : p i <;> simp [h,ih]

theorem first_error (p : Nat → Bool) (count : Nat) (out : Option Nat)
    (h : Trace p count 0 out) : out = LPt_LPl_A.firstBad (fun i => !p i) count := by
  rw [result p count 0 out h,Nat.sub_zero,run_find,LPt_LPl_A.firstBad_find]
  rw [List.range_eq_range']

theorem unique (p : Nat → Bool) (count i : Nat) (a b : Option Nat)
    (left : Trace p count i a) (right : Trace p count i b) : a = b :=
  (result p count i a left).trans (result p count i b right).symm

theorem exists_trace (p : Nat → Bool) (n i count : Nat)
    (remaining : count-i=n) (bound : i ≤ count) : ∃ out, Trace p count i out := by
  induction n generalizing i with
  | zero => exact ⟨none,.done i (by omega)⟩
  | succ n ih =>
    have live : i < count := by omega
    cases h : p i with
    | false => exact ⟨some i,.reject i live h⟩
    | true =>
      obtain ⟨out,rest⟩ := ih (i+1) (by omega) (by omega)
      exact ⟨out,.next i live h out rest⟩

/-- Explicit local carrier association used to construct p at the reached
    iterator pre-state. Byte equality identifies the backing, not just length. -/
structure Window (bs : List U8) (width i : Nat) where
  offset : Nat
  remaining : Nat
  bytes : List U8
  pointer : offset = width*i
  count : remaining = bs.length/width-i
  sameBytes : bytes = (bs.drop offset).take width

theorem window_eq (bs : List U8) (width i : Nat) (w : Window bs width i)
    (decoder : List U8 → Bool) :
    decoder w.bytes = decoder ((bs.drop (width*i)).take width) := by
  rw [w.sameBytes,w.pointer]

/-- The inherited Boolean loop and the exact first-error scan reject on the
    same index set. No accepted-only hypothesis. -/
theorem bool_none (p : Nat → Bool) (count : Nat) :
    LPt_LPl_A.stages (fun good i => good && p i) true count =
      (LPt_LPl_A.firstBad (fun i => !p i) count).isNone := by
  have eq : LPt_LPl_A.stages (fun good i => good && p i) true count = true ↔
      LPt_LPl_A.firstBad (fun i => !p i) count = none := by
    rw [LPt_LPl_A.stages_all,List.all_eq_true,LPt_LPl_A.firstBad_none]
    simp only [List.mem_range]
    constructor
    · intro h i hi; rw [h i hi]; rfl
    · intro h i hi; have := h i hi; cases q : p i <;> simp_all
  cases a : LPt_LPl_A.stages (fun good i => good && p i) true count <;>
    cases b : LPt_LPl_A.firstBad (fun i => !p i) count <;> simp_all

#print axioms result
#print axioms run_find
#print axioms first_error
#print axioms unique
#print axioms exists_trace
#print axioms window_eq
#print axioms bool_none
end LPt_LPl.Scan
