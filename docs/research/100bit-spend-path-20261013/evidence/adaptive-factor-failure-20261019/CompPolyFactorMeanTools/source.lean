import CompPolyFactorOracleProgram
import R1GenericNoHitFS2
import FS.LemmaA

/-! Lightweight outcome adapters for the existing independent-answer
interpreter. The const/congruence proof shapes are reused from
AspisV8R19.R572SequentialWordMass, avoiding its unrelated rejection-sampler
imports; monotonicity and scalar linearity apply the existing FS lemmas. -/
noncomputable section
namespace AspisR1.CompPolyFactorMeanTools
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
variable {I A O R : Type} [Fintype A] [Nonempty A]

def outMean (p : Program I A O) (observe : O → ℚ) : ℚ :=
  independentMean p (fun v => observe v.2)

theorem outMean_congr (p : Program I A O) {f g : O → ℚ} (h : ∀ o, f o = g o) :
    outMean p f = outMean p g := by
  induction p with
  | done o => exact h o
  | ask i next ih =>
    change mean (fun a => outMean (next a) f) = mean (fun a => outMean (next a) g)
    exact mean_congr (fun a => ih a)

theorem outMean_const (p : Program I A O) (c : ℚ) :
    outMean p (fun _ => c) = c := by
  induction p with
  | done o => rfl
  | ask i next ih =>
    change mean (fun a => outMean (next a) (fun _ => c)) = c
    rw [mean_congr (fun a => ih a)]
    exact mean_const c

theorem outMean_mono (p : Program I A O) {f g : O → ℚ}
    (h : ∀ o, f o ≤ g o) : outMean p f ≤ outMean p g :=
  GenericNoHitFS2.independentMean_mono p _ _ (fun v => h v.2)

theorem outMean_add_const (p : Program I A O) (f : O → ℚ) (c : ℚ) :
    outMean p (fun o => f o+c) = outMean p f+c := by
  induction p with
  | done o => rfl
  | ask i next ih =>
    change mean (fun a => outMean (next a) (fun o => f o+c)) =
      mean (fun a => outMean (next a) f)+c
    rw [mean_congr (fun a => ih a), FS.mean_add, mean_const]

theorem outMean_bind (p : Program I A O) (next : O → Program I A R) (f : R → ℚ) :
    outMean (bind p next) f = outMean p (fun o => outMean (next o) f) := by
  exact independentMean_bind p next (fun v => f v.2)

def abortIndicator {X : Type} (o : Option X) : ℚ := if o.isSome then 0 else 1

theorem bind_abort_le (p : Program I A (Option O))
    (next : O → Program I A (Option R)) (B : ℚ) (hB : 0 ≤ B)
    (hnext : ∀ o, outMean (next o) abortIndicator ≤ B) :
    outMean (bind p (fun o => match o with
      | none => .done none | some x => next x)) abortIndicator ≤
      outMean p abortIndicator+B := by
  rw [outMean_bind, ← outMean_add_const]
  apply outMean_mono
  intro o
  cases o with
  | none =>
    change (1 : ℚ) ≤ 1+B
    exact le_add_of_nonneg_right hB
  | some o =>
    simpa only [abortIndicator, Option.isSome_some, ↓reduceIte, zero_add] using hnext o

#print axioms outMean_mono
#print axioms outMean_const
#print axioms outMean_bind
#print axioms bind_abort_le
end AspisR1.CompPolyFactorMeanTools
