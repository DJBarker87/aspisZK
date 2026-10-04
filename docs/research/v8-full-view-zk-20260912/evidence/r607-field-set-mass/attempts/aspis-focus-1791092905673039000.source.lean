import AspisV8R19.R601ExactFieldMass

set_option autoImplicit false
namespace AspisV8R19.R607FieldSetMass
open MemoizedProgramLaw OracleResampling AdaptiveFirstReadLaw
open R601ExactFieldMass R599CanonicalFieldTuple R584IndependentBlockSampler
open R445InitialBlockRejectionLaw SourceDuplexStep QM31SamplerProgram
open AspisV8R15.ExactTowerBase
open scoped BigOperators
noncomputable section

abbrev Tuple := Fin 4 → Fin modulus

def setEvent (S : Finset Tuple) (out : Option (List Nat)) : ℚ :=
  if ∃ x ∈ S, out.map SamplerFieldDecode.decode = some (tupleField x) then 1 else 0

theorem set_event_partition (S : Finset Tuple) (out : Option (List Nat)) :
    setEvent S out = ∑ x ∈ S, fieldEvent (tupleField x) out := by
  classical
  cases out with
  | none => simp [setEvent, fieldEvent]
  | some xs =>
      let x0 := tupleFieldEquiv.symm (SamplerFieldDecode.decode xs)
      have h0 : tupleField x0 = SamplerFieldDecode.decode xs :=
        tupleFieldEquiv.apply_symm_apply _
      have heq : ∀ x : Tuple, SamplerFieldDecode.decode xs = tupleField x ↔ x = x0 := by
        intro x
        constructor
        · intro h
          exact (tupleFieldEquiv.injective (h0.trans h)).symm
        · intro h
          subst x
          exact h0.symm
      simp only [setEvent, fieldEvent, Option.map_some, Option.some.injEq, heq]
      simp

theorem mean_finset_sum {X Y : Type} [Fintype X]
    (S : Finset Y) (f : Y → X → ℚ) :
    mean (fun x => ∑ y ∈ S, f y x) = ∑ y ∈ S, mean (f y) := by
  simp only [mean, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem outputMean_finset_sum {I A O X : Type} [Fintype A]
    (p : Program I A O) (S : Finset X) (f : X → O → ℚ) :
    outputMean p (fun o => ∑ x ∈ S, f x o) = ∑ x ∈ S, outputMean p (f x) := by
  induction p with
  | done o => rfl
  | ask i next ih =>
      change mean (fun a => outputMean (next a) (fun o => ∑ x ∈ S, f x o)) =
        ∑ x ∈ S, mean (fun a => outputMean (next a) (f x))
      calc
        _ = mean (fun a => ∑ x ∈ S, outputMean (next a) (f x)) :=
          mean_congr (fun a => ih a)
        _ = _ := mean_finset_sum S _

theorem source_independent_set_mass (s : State) (S : Finset Tuple) :
    outputMean (challengeProgram s) (fun r => setEvent S r.1) =
      (S.card : ℚ) * ((1-(1/(2147483648 : ℚ))^8)/2147483647)^4 := by
  have hp : (fun r : Option (List Nat) × State => setEvent S r.1) =
      (fun r => ∑ x ∈ S, fieldEvent (tupleField x) r.1) := by
    funext r
    exact set_event_partition S r.1
  rw [hp, outputMean_finset_sum]
  simp only [source_independent_field_mass, Finset.sum_const, nsmul_eq_mul,
    Finset.card_eq_sum_ones]

#print axioms set_event_partition
#print axioms mean_finset_sum
#print axioms outputMean_finset_sum
#print axioms source_independent_set_mass
end
end AspisV8R19.R607FieldSetMass
