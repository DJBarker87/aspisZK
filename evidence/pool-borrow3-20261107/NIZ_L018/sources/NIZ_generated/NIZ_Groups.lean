import NIZ_Unique
set_option autoImplicit false
namespace NIZ_Groups

/-- The original prefixRows-any uniqueness helper accepts iff all earlier rows
have no equal key. Its one predicate step is NIZ_K023/K024. -/
def prefixRows {Key : Type} [DecidableEq Key] (key : Nat → Key) : Nat → Bool
  | 0 => true
  | n+1 => prefixRows key n && NIZ_Unique.row key n 0 n

theorem prefix_distinct {Key : Type} [DecidableEq Key] (key : Nat → Key)
    (n : Nat) (ok : prefixRows key n = true) :
    ∀ i j, i < n → j < n → i ≠ j → key i ≠ key j := by
  induction n with
  | zero => intro i j hi; omega
  | succ n ih =>
    have hs : prefixRows key n = true ∧ NIZ_Unique.row key n 0 n = true := by
      simpa only [prefixRows,Bool.and_eq_true_iff] using ok
    apply NIO_Cpi.uniqueness_step key n (ih hs.1)
    intro i hi
    have h := NIZ_Unique.row_sound key n 0 n hs.2 i hi
    exact Ne.symm (by simpa using h)
#print axioms prefix_distinct

/-- Logical merged view of two separate account groups; no native index addition
or new native memory region is introduced. -/
def view {Key : Type} (states tokens : Nat → Key) (i : Nat) : Nat → Key
  | 0 => states i
  | j+1 => tokens j

def groupRows {Key : Type} [DecidableEq Key] (states tokens : Nat → Key)
    (tokenCount start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => NIZ_Unique.row (view states tokens start) 0 1 tokenCount &&
      groupRows states tokens tokenCount (start+1) n

theorem group_rows_sound {Key : Type} [DecidableEq Key] (states tokens : Nat → Key)
    (tokenCount start count : Nat)
    (ok : groupRows states tokens tokenCount start count = true) :
    ∀ i j, start ≤ i → i < start+count → j < tokenCount → states i ≠ tokens j := by
  induction count generalizing start with
  | zero => intro i j hi hc; omega
  | succ n ih =>
    have hs : NIZ_Unique.row (view states tokens start) 0 1 tokenCount = true ∧
        groupRows states tokens tokenCount (start+1) n = true := by
      simpa only [groupRows,Bool.and_eq_true_iff] using ok
    intro i j hi hc hj
    by_cases eq : i = start
    · subst i
      have h := NIZ_Unique.row_sound (view states tokens start) 0 1 tokenCount hs.1 j hj
      simpa [view,Nat.add_comm] using h
    · exact ih (start+1) hs.2 i j (by omega) (by omega) hj
#print axioms group_rows_sound

/-- Exact mathematical conclusion of successful cross-group uniqueness.
Native whole-helper/source and SAME caller-group association are separate. -/
theorem groups_distinct {Key : Type} [DecidableEq Key] (states tokens : Nat → Key)
    (stateCount tokenCount : Nat)
    (ok : groupRows states tokens tokenCount 0 stateCount = true) :
    ∀ i j, i < stateCount → j < tokenCount → states i ≠ tokens j := by
  intro i j hi hj
  exact group_rows_sound states tokens tokenCount 0 stateCount ok i j (by omega) (by omega) hj
#print axioms groups_distinct
end NIZ_Groups
