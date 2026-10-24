import S9ConstructorV3CarryBodySemanticsV1
import Query31ArrayReadback
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3VectorMeaningV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3CarryBodySemanticsV1
abbrev ExactQM := AspisR1.ExtractedCurrentQM31Exact.QM31Exact

/-- Coordinates retain the source's MSB-first order. -/
def Meaning (a : Vector) (p : Nat → ExactQM) : Prop :=
  ∀ (i : Usize) (q : AspisR1S9ConstructorV3Loop2InnerCanonicalV1.Q),
    Array.index_usize a i = .ok q → decode q = p i.val

private theorem index_success_bound (a : Vector) (i : Usize)
    (q : AspisR1S9ConstructorV3Loop2InnerCanonicalV1.Q)
    (h : Array.index_usize a i = .ok q) : i.val < 10 := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
    have hsome : a.val[i.val]? = some y := by simpa using hopt
    have hlen := (List.getElem?_eq_some_iff.mp hsome).1
    simpa only [a.property] using hlen

/-- Exact read meaning after the same actual successful mutable array write. -/
theorem update_meaning (a out : Vector) (i : Usize)
    (cell : AspisR1S9ConstructorV3Loop2InnerCanonicalV1.Q) (p : Nat → ExactQM)
    (hinput : Meaning a p) (hupdate : Array.update a i cell = .ok out) :
    Meaning out (Function.update p i.val (decode cell)) := by
  have hi := AspisR1S9ConstructorV3StatementCellCanonicalV1.update_success_bound a i cell out hupdate
  intro j q hread
  have hj := index_success_bound out j q hread
  by_cases he : j = i
  · subst j
    have hwrite := AspisR1PublicPreparation.Query31SourceSchedule.update_readback a i cell hi out hupdate
    have hv : cell = q := Result.ok.inj (hwrite.symm.trans hread)
    rw [Function.update_self,hv]
  · have hv : j.val ≠ i.val := by
      intro heq
      exact he (UScalar.eq_of_val_eq heq)
    have hs := AspisR1PublicPreparation.Query31SourceSchedule.update_readback_other
      a i j cell (Ne.symm he) hi hj out hupdate
    rw [Function.update_of_ne hv]
    exact hinput j q (hs.symm.trans hread)

/-- Nat-coordinate version of the retained SemView.succCarry definition. The
only change is replacing p's dependent Fin index with its natural coordinate. -/
def succCarry (p : Nat → ExactQM) : Nat → ExactQM
  | 0 => 1
  | k+1 => (if k < 10 then p (9-k) else 0) * succCarry p k

def successorPoint (p : Nat → ExactQM) (c : Nat) : ExactQM :=
  let carry := succCarry p (9-c)
  p c + carry - (p c * carry + p c * carry)

/-- Symbolic recurrence reused from ProverCommitSuccessorPoint49.carry_step. -/
theorem carry_step (p : Nat → ExactQM) (n : Nat) (hn : n<10) :
    succCarry p (10-n) = p n * succCarry p (9-n) := by
  have he : 10-n = (9-n)+1 := by omega
  rw [he,succCarry,if_pos (by omega)]
  have hi : 9-(9-n)=n := by omega
  rw [hi]

#print axioms update_meaning
#print axioms carry_step
end AspisR1S9ConstructorV3VectorMeaningV1
