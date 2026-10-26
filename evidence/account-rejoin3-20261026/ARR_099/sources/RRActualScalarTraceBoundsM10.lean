import RRActualScalarTraceM10
import GSScalarAtBoundsM10
import GSScalarJobsM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.RRActualScalarTraceBoundsM10
open CompPoly RRConcreteState RRConcreteValidState RRActualScalarTraceM10
open GSScalarCallScheduleM10 GSScalarOperandEnvelopeM10
open AspisV8R19.MemoizedProgramLaw
open SequentialProgramInvariants SequentialFreshProgram
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem child_length (ell q t : Nat) (H : Nat → Fin t → K × K)
    (s : ValidState ell K) (cursor : Nat) (hq : q = Fintype.card K) :
    ((children ell q t H s cursor).1.1.getD []).length ≤ ell := by
  have h := all_eval H _ _ (all_sequential _ _
    (RRConcreteWriterM10.children_length ell q t s hq) cursor)
  rw [← children_value] at h
  exact h

theorem child_trace_length (ell q t : Nat) (H : Nat → Fin t → K × K)
    (s : ValidState ell K) (cursor : Nat) :
    (children ell q t H s cursor).2.length ≤ GSScalarAtBoundsM10.budget t ell := by
  apply GSScalarAtBoundsM10.length
  rw [scalarPolynomial_toPoly]
  exact s.property.2 0 (Nat.zero_le _)

theorem child_bounded (ell q t : Nat) (H : Nat → Fin t → K × K)
    (s : ValidState ell K) (cursor : Nat) (hell : 1 ≤ ell) :
    ∀ c ∈ (children ell q t H s cursor).2, Bounded ell q c := by
  apply GSScalarAtCursorM10.bounded
  · rw [scalarPolynomial_toPoly]
    exact s.property.2 0 (Nat.zero_le _)
  · exact hell

theorem walk_length {S : Type} (run : S → Nat → Result K) (N : Nat)
    (h : ∀ s c, (run s c).2.length ≤ N) (xs : List (K × S)) (cursor : Nat) :
    (walk run xs cursor).2.length ≤ xs.length*N := by
  induction xs generalizing cursor with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    rcases x with ⟨a,s⟩
    have hh := h s cursor
    have ht := ih (run s cursor).1.2
    simp only [walk]
    split <;> dsimp only <;> simp only [List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul] <;> omega

theorem walk_bounded {S : Type} (run : S → Nat → Result K) (P : Call K → Prop)
    (h : ∀ s c, ∀ x ∈ (run s c).2, P x) (xs : List (K × S)) (cursor : Nat) :
    ∀ x ∈ (walk run xs cursor).2, P x := by
  induction xs generalizing cursor with
  | nil => simp [walk]
  | cons x xs ih =>
    rcases x with ⟨a,s⟩
    simp only [walk]
    split
    · exact h s cursor
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h s cursor x hx
      · exact ih (run s cursor).1.2 x hx

def budget (ell t : Nat) : Nat → Nat
  | 0 => 0
  | d+1 => GSScalarAtBoundsM10.budget t ell+ell*budget ell t d

theorem length (ell q t : Nat) (H : Nat → Fin t → K × K) (d : Nat)
    (s : ValidState ell K) (cursor : Nat) (hq : q = Fintype.card K) :
    (collect ell q t H d s cursor).2.length ≤ budget ell t d := by
  induction d generalizing s cursor with
  | zero => exact Nat.zero_le _
  | succ d ih =>
    have hc := child_trace_length ell q t H s cursor
    have hl := child_length ell q t H s cursor hq
    simp only [collect,budget]
    split
    · exact hc.trans (Nat.le_add_right _ _)
    · rename_i cs hs
      have hcs : cs.length ≤ ell := by simpa only [hs,Option.getD_some] using hl
      have hw := (walk_length (collect ell q t H d) (budget ell t d) ih cs
        (children ell q t H s cursor).1.2).trans (Nat.mul_le_mul_right _ hcs)
      simpa only [List.length_append] using Nat.add_le_add hc hw

theorem bounded (ell q t : Nat) (H : Nat → Fin t → K × K) (d : Nat)
    (s : ValidState ell K) (cursor : Nat) (hell : 1 ≤ ell) :
    ∀ c ∈ (collect ell q t H d s cursor).2, Bounded ell q c := by
  induction d generalizing s cursor with
  | zero => simp [collect]
  | succ d ih =>
    have hc := child_bounded ell q t H s cursor hell
    simp only [collect]
    split
    · exact hc
    · rename_i cs hs
      intro c hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hc c hmem
      · exact walk_bounded (collect ell q t H d) (Bounded ell q) ih cs
          (children ell q t H s cursor).1.2 c hmem

theorem jobs (ell q t : Nat) (H : Nat → Fin t → K × K) (d : Nat)
    (s : ValidState ell K) (cursor : Nat) (hq : q = Fintype.card K) (hell : 1 ≤ ell) :
    ∃ j : RawExtractorCostLedger.Jobs K,
      j.Bounded (ell+1) (q+1) (budget ell t d) := by
  have hb := bounded ell q t H d s cursor hell
  have hj := GSScalarJobsM10.bounded ell q _ hb
  have hl := length ell q t H d s cursor hq
  refine ⟨GSScalarJobsM10.ofCalls ell q _ hb,?_⟩
  exact ⟨hj.gcd_count.trans hl,hj.division_count.trans hl,hj.power_count.trans hl,
    hj.gcd_sizes,hj.division_sizes,hj.power_bits⟩

#print axioms child_length
#print axioms child_trace_length
#print axioms child_bounded
#print axioms walk_length
#print axioms walk_bounded
#print axioms length
#print axioms bounded
#print axioms jobs
end AspisR1.RRActualScalarTraceBoundsM10
end
