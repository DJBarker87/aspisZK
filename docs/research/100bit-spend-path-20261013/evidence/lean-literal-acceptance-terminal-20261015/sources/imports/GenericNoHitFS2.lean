import R1GenericNoHit
import FS2.Statement

/-! Generic FS2 bookkeeping for the table-independent no-hit classifier.
The row-density and terminal implication remain explicit hypotheses. This
module does not establish either for the selected spend protocol. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.GenericNoHitFS2

open FS FS2 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
attribute [local instance] Classical.propDecidable

variable {X M C W Pf I A O : Type}

/-- Monotonicity of the existing independent-answer interpreter. -/
theorem independentMean_mono [Fintype A] (p : Program I A O)
    (f g : View I A O → ℚ) (h : ∀ v, f v ≤ g v) :
    independentMean p f ≤ independentMean p g := by
  induction p generalizing f g with
  | done o => exact h ([], o)
  | ask i next ih =>
      change mean (fun a => independentMean (next a) _) ≤
        mean (fun a => independentMean (next a) _)
      apply mean_mono
      intro a
      exact ih a _ _ (fun v => h ((i,a) :: v.1, v.2))

def rows (bad : Prefix X M C → M → C → Prop) (relation : X → W → Prop)
    (eps : Nat → ℚ) : RoundByRound' X M C I A where
  doomed := fun P _ => GenericNoHit.doomed bad relation P
  ε := eps

theorem d1 [DecidableEq I] [Inhabited A] [Fintype A]
    (pr : Protocol X M C W Pf I A)
    (bad : Prefix X M C → M → C → Prop) (relation : X → W → Prop)
    (eps : Nat → ℚ)
    (hextract : ∀ x T, pr.extract x T = GenericNoHit.chooseWitness relation x) :
    D1 pr (rows bad relation eps) := by
  intro x T h
  change GenericNoHit.doomed bad relation (emptyPrefix x)
  apply (GenericNoHit.empty_doomed bad relation x).mpr
  rw [← hextract x T]
  exact h

/-- Pointwise escape containment is independent of both tables. The supplied
fixed-prefix density must still be proved for every applicable message. -/
theorem d2 [DecidableEq I] [Inhabited A] [Fintype A]
    (pr : Protocol X M C W Pf I A)
    (bad : Prefix X M C → M → C → Prop) (relation : X → W → Prop)
    (eps : Nat → ℚ)
    (hdensity : ∀ i P m, P.round = i → i < pr.r →
      GenericNoHit.doomed bad relation P →
      independentMean (pr.samp i P m).toProgram
        (fun v => indicator (bad P m v.2)) ≤ eps i) :
    D2 pr (rows bad relation eps) := by
  intro i P m T' T hr hi hd
  apply le_trans _ (hdensity i P m hr hi hd)
  apply independentMean_mono
  intro v
  apply indicator_mono
  exact GenericNoHit.doomed_ext_bad bad relation P m v.2 hd

/-- The terminal accepted/no-hit implication suffices for D3. It is not
supplied by the generic classifier construction. -/
theorem d3 [DecidableEq I] [Inhabited A] [Fintype A]
    (pr : Protocol X M C W Pf I A)
    (bad : Prefix X M C → M → C → Prop) (relation : X → W → Prop)
    (eps : Nat → ℚ) (V : X → Pf → Program I A Bool)
    (hterminal : ∀ H x pf, (eval H (V x pf)).2 = true →
      ¬ GenericNoHit.hitFrom bad x [] (pr.transcript H x pf pr.r).rounds →
      ∃ w, relation x w) :
    D3 pr (rows bad relation eps) V := by
  intro H x pf T hd
  by_cases hacc : (eval H (V x pf)).2 = true
  · have hx : (pr.transcript H x pf pr.r).statement = x := by
      have aux : ∀ n, (pr.transcript H x pf n).statement = x := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => exact ih
      exact aux pr.r
    have hno : ¬ GenericNoHit.hitFrom bad x [] (pr.transcript H x pf pr.r).rounds := by
      simpa only [hx] using hd.2
    have hrel : ¬ ∃ w, relation x w := by simpa only [hx] using hd.1
    exact (hrel (hterminal H x pf hacc hno)).elim
  · exact Bool.eq_false_iff.mpr hacc

#print axioms independentMean_mono
#print axioms d1
#print axioms d2
#print axioms d3

end AspisR1.GenericNoHitFS2
end
