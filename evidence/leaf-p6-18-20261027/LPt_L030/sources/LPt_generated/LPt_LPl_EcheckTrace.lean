import LPt_LPl_EcheckBytes
open Aeneas Aeneas.Std Result LPt_LPl_Kit_Release
set_option autoImplicit false
namespace LPt_LPl.Echeck
/-- One immutable chunks_exact pre-state. `offset` is the byte displacement of
    its pointer into the SAME backing; `remaining` is the actual chunk count. -/
structure Cursor (bs : List U8) where
  index : Nat
  offset : Nat
  remaining : Nat
  pointer : offset = 32*index
  count : remaining = bs.length/32-index
  bound : index ≤ bs.length/32

def cursor (bs : List U8) (i : Nat) (h : i ≤ bs.length/32) : Cursor bs :=
  ⟨i,32*i,bs.length/32-i,rfl,rfl,h⟩

def read (bs : List U8) (s : Cursor bs) : List U8 := (bs.drop s.offset).take 32

theorem read_eq (bs : List U8) (s : Cursor bs) :
    read bs s = (bs.drop (32*s.index)).take 32 := by rw [read,s.pointer]

theorem read_size (bs : List U8) (s : Cursor bs) (live : 0 < s.remaining) :
    (read bs s).length = 32 := by
  have hi : s.index < bs.length/32 := by have := s.count; omega
  have mul := Nat.mul_le_mul_left 32 (Nat.succ_le_iff.mpr hi)
  have div := Nat.div_mul_le_self bs.length 32
  rw [read_eq, List.length_take, List.length_drop]
  omega

theorem advance (bs : List U8) (s : Cursor bs) (live : 0 < s.remaining) :
    ∃ t : Cursor bs, t.index = s.index+1 ∧ t.offset = s.offset+32 ∧
      t.remaining+1 = s.remaining := by
  have hi : s.index < bs.length/32 := by have := s.count; omega
  refine ⟨cursor bs (s.index+1) (by omega),rfl,?_,?_⟩
  · simp only [cursor]; rw [s.pointer]; omega
  · simp only [cursor]; rw [s.count]; omega

/-- Source-shaped execution: exact next window/count, local decoder Result,
    immediate Parse rejection, and no decoder invocation on the empty suffix.
    There is no whole-output equality field. Native gates construct this trace. -/
inductive Trace (bs : List U8) (k : Bool) : Nat → Bool → Prop where
  | done (i : Nat) (endOfIterator : i = bs.length/32) : Trace bs k i true
  | reject (s : Cursor bs) (live : 0 < s.remaining)
      (nativeWindow : List U8) (sameWindow : nativeWindow = read bs s)
      (rejected : chunk nativeWindow k = false) : Trace bs k s.index false
  | next (s t : Cursor bs) (live : 0 < s.remaining)
      (nativeWindow : List U8) (sameWindow : nativeWindow = read bs s)
      (accepted : chunk nativeWindow k = true)
      (indexNext : t.index = s.index+1) (pointerNext : t.offset = s.offset+32)
      (countNext : t.remaining+1 = s.remaining)
      (result : Bool) (rest : Trace bs k t.index result) : Trace bs k s.index result

/-- Remaining-source semantics; induction follows the decreasing actual count. -/
def run (bs : List U8) (k : Bool) (i : Nat) : Nat → Bool
  | 0 => true
  | n+1 => chunk ((bs.drop (32*i)).take 32) k && run bs k (i+1) n

theorem trace_result (bs : List U8) (k : Bool) (i : Nat) (out : Bool)
    (h : Trace bs k i out) : out = run bs k i (bs.length/32-i) := by
  induction h with
  | done i endOfIterator => simp [endOfIterator,run]
  | reject s live w same bad =>
    have hi : s.index < bs.length/32 := by have := s.count; omega
    have hn : bs.length/32-s.index = (bs.length/32-s.index-1)+1 := by omega
    rw [hn,run]
    rw [same,read_eq] at bad
    simp only [bad,Bool.false_and]
  | next s t live w same good indexNext pointerNext countNext result rest ih =>
    have hi : s.index < bs.length/32 := by have := s.count; omega
    have hn : bs.length/32-s.index = (bs.length/32-t.index)+1 := by omega
    rw [hn,run]
    rw [same,read_eq] at good
    rw [good,Bool.true_and,← indexNext]
    exact ih

#print axioms read_eq
#print axioms read_size
#print axioms advance
#print axioms trace_result
end LPt_LPl.Echeck
