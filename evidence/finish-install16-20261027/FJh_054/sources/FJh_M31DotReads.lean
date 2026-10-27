import FJh_M31DotSource
import FJh_InternalStateWords

/-! Actual input slice reads and a proof-index-free natural term view for
symbolic chunk invariants. The term view is tied to both actual reads. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotReads
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base (QM Canonical cell)
open AspisR1.FJh_InternalStateWords (wordVec)

def sliceCell {T : Type} (s : Slice T) (i : Nat) (hi : i < s.val.length) : T := s.val[i]'hi

def CanonicalWeights (weights : Slice QM) : Prop :=
  ∀ (i : Nat) (hi : i < weights.val.length), Canonical (sliceCell weights i hi)
def CanonicalValues (values : Slice U32) : Prop :=
  ∀ (i : Nat) (hi : i < values.val.length), (sliceCell values i hi).val < AspisV8R17.RawReducer.P

theorem source_read {T : Type} (s : Slice T) (i : Usize) (hi : i.val < s.val.length) :
    Slice.index_usize s i = .ok (sliceCell s i.val hi) := by
  unfold Slice.index_usize
  change (match s.val[i.val]? with
    | none => (Result.fail Error.arrayOutOfBounds : Result T)
    | some x => Result.ok x) = Result.ok (s.val[i.val]'hi)
  rw [List.getElem?_eq_getElem hi]

def term (weights : Slice QM) (values : Slice U32) (i : Nat) (j : Fin 4) : Nat :=
  match weights.val[i]?, values.val[i]? with
  | some q, some v => (cell (wordVec q) j).val * v.val
  | _, _ => 0

theorem term_read (weights : Slice QM) (values : Slice U32) (i : Usize)
    (hw : i.val < weights.val.length) (hv : i.val < values.val.length) (j : Fin 4) :
    term weights values i.val j =
      (cell (wordVec (sliceCell weights i.val hw)) j).val * (sliceCell values i.val hv).val := by
  unfold term
  rw [List.getElem?_eq_getElem hw,List.getElem?_eq_getElem hv]
  rfl

def remaining (weights : Slice QM) (values : Slice U32) (start fuel : Nat) (j : Fin 4) : Nat :=
  match fuel with
  | 0 => 0
  | n+1 => term weights values start j + remaining weights values (start+1) n j

#print axioms source_read
#print axioms term_read
end AspisR1.FJh_M31DotReads
