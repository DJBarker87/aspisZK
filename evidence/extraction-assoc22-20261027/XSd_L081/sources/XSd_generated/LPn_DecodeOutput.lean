import LPn_DecodeBytes
open Aeneas Aeneas.Std Result LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPn.Decode
abbrev Q := aspis_core.field.QM31

def value (bs : List U8) (start i : Nat) : Q := (LPn.DecodeModel.step bs start i).2

def predicate (bs : List U8) (start count i : Nat) : Bool :=
  ((LPn.DecodeModel.values bs start count)[i]?.getD (true,qzero)).1

theorem predicate_eq (bs : List U8) (start count i : Nat) (live : i<count) :
    predicate bs start count i = (LPn.DecodeModel.step bs start i).1 := by
  simp [predicate,LPn.DecodeModel.values_eq_map,live]

structure Write (bs : List U8) (start row : Nat) (before after : List Q) : Prop where
  length : after.length=before.length
  bytes : ∀ j, j<before.length → after[j]?.getD qzero =
    if j=row then value bs start row else before[j]?.getD qzero

inductive Trace (bs : List U8) (start : Nat) (initial : List Q) : Nat → List Q → Prop where
  | init : Trace bs start initial 0 initial
  | next (i : Nat) (before after : List Q) (rest : Trace bs start initial i before)
      (write : Write bs start i before after) : Trace bs start initial (i+1) after

theorem length (bs : List U8) (start : Nat) (initial after : List Q) (n : Nat)
    (trace : Trace bs start initial n after) : after.length=initial.length := by
  induction trace with
  | init => rfl
  | next i before after rest write ih => exact write.length.trans ih

theorem invariant (bs : List U8) (start : Nat) (initial after : List Q) (n : Nat)
    (trace : Trace bs start initial n after) :
    ∀ j, j < initial.length → after[j]?.getD qzero =
      if j < n then value bs start j else initial[j]?.getD qzero := by
  induction trace with
  | init => intro j hj; simp
  | next i before after rest write ih =>
    intro j hj
    have size := length bs start initial before i rest
    rw [write.bytes j (by omega)]
    by_cases eq : j=i
    · subst j; simp
    · rw [if_neg eq,ih j hj]
      by_cases lt : j < i
      · rw [if_pos lt,if_pos (by omega)]
      · rw [if_neg lt,if_neg (by omega)]

theorem output (bs : List U8) (start : Nat) (initial after : List Q) (n : Nat)
    (trace : Trace bs start initial n after) (done : initial.length=n) :
    after=(LPn.DecodeModel.values bs start n).map Prod.snd := by
  have size := length bs start initial after n trace
  apply List.ext_getElem
  · simp only [List.length_map,LPn.DecodeModel.values_length];omega
  · intro j hj hk
    have bound : j < n := by omega
    have h := invariant bs start initial after n trace j (by omega)
    rw [if_pos bound] at h
    simpa [List.getElem?_eq_getElem hj,LPn.DecodeModel.values_eq_map,value,bound] using h

theorem unique (bs : List U8) (start : Nat) (initial a b : List Q) (n : Nat)
    (done : initial.length=n) (left : Trace bs start initial n a)
    (right : Trace bs start initial n b) : a=b :=
  (output bs start initial a n left done).trans (output bs start initial b n right done).symm

def update (bs : List U8) (start row : Nat) (before : List Q) : List Q :=
  (List.range before.length).map fun j =>
    if j=row then value bs start row else before[j]?.getD qzero

theorem update_write (bs : List U8) (start row : Nat) (before : List Q) :
    Write bs start row before (update bs start row before) := by
  constructor
  · simp only [update,List.length_map,List.length_range]
  · intro j hj; simp [update,hj]

theorem total (bs : List U8) (start : Nat) (initial : List Q) (n : Nat) :
    ∃ after, Trace bs start initial n after := by
  induction n with
  | zero => exact ⟨initial,.init⟩
  | succ n ih =>
    obtain ⟨before,trace⟩ := ih
    exact ⟨update bs start n before,.next n before _ trace (update_write bs start n before)⟩

/-- Rebase a selected array cell to the three-cell native frame harness. -/
def coordinate (row j : Nat) : Nat := if j<row then 0 else if j=row then 1 else 2

theorem coordinate_bound (row j : Nat) : coordinate row j < 3 := by
  unfold coordinate
  split
  · omega
  · split <;> omega

theorem coordinate_written (row j : Nat) : coordinate row j=1 ↔ j=row := by
  by_cases lt : j < row
  · simp [coordinate,lt,show j≠row by omega]
  · simp [coordinate,lt]

theorem write_of_local (bs : List U8) (start row : Nat) (before after : List Q)
    (size : after.length=before.length)
    (observed : ∀ j, j<before.length → after[j]?.getD qzero =
      if coordinate row j=1 then value bs start row else before[j]?.getD qzero) :
    Write bs start row before after := by
  refine ⟨size,?_⟩
  intro j hj
  simpa only [coordinate_written] using observed j hj

#print axioms update_write
#print axioms total
#print axioms coordinate_bound
#print axioms coordinate_written
#print axioms write_of_local
#print axioms predicate_eq
#print axioms length
#print axioms invariant
#print axioms output
#print axioms unique
end LPn.Decode
