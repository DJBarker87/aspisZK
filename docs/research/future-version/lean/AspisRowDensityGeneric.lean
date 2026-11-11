import R0C.ModuloCounting

/-! Aspis per-step accounting, row densities: the generic sampler lemma.

Kind of result: a theorem in R1's sampler setting (the balanced modulo
reduction `R0C.ModuloCounting.reduce` read through two encoding
equivalences), with no protocol, transcript or Aspis object in it.

R1 states the sampler mass of the reduced challenge only for its row-32
residual set, with the constant 21 (`AspisR1.RhoSamplerBound.modulo_bad_mass`).
R1's `R0C.ModuloCounting.event_mass_le` is the general per-set union bound and
`encoded_mass_le` the per-element bound; R1 composes them only for that one
set. `modulo_set_mass` composes them for an arbitrary finite set `S` of the
output type, giving `|S| * ((B / n + 1) / B)`. R1's statement is recovered from
it as a corollary in `AspisRowDensityQM31.modulo_bad_mass_recovered`. -/

set_option autoImplicit false
noncomputable section

namespace AspisRowDensity.Generic

open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound

/-- The mass of "the reduced sample lies in `S`" is at most `|S|` times the
largest fibre mass `(B / n + 1) / B`. `S` is any finite set of outputs; it is
a fixed parameter, quantified outside the mean. -/
theorem modulo_set_mass {A K : Type} [Fintype A] [Fintype K] {B n : Nat} (hn : 0 < n)
    (input : A ≃ Fin B) (output : Fin n ≃ K) (S : Finset K) :
    mean (fun a : A => indicator
      (output (R0C.ModuloCounting.reduce hn (input a)) ∈ S)) ≤
      (S.card : ℚ) * (((B / n + 1 : Nat) : ℚ) / B) :=
  R0C.ModuloCounting.event_mass_le
    (fun a : A => output (R0C.ModuloCounting.reduce hn (input a)))
    (((B / n + 1 : Nat) : ℚ) / B)
    (R0C.ModuloCounting.encoded_mass_le hn input output) S

/-- The same with a cardinality hypothesis `|S| ≤ k`. -/
theorem modulo_set_mass_le {A K : Type} [Fintype A] [Fintype K] {B n : Nat} (hn : 0 < n)
    (input : A ≃ Fin B) (output : Fin n ≃ K) (S : Finset K) (k : Nat)
    (hS : S.card ≤ k) :
    mean (fun a : A => indicator
      (output (R0C.ModuloCounting.reduce hn (input a)) ∈ S)) ≤
      (k : ℚ) * (((B / n + 1 : Nat) : ℚ) / B) := by
  apply (modulo_set_mass hn input output S).trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hS
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

#print axioms modulo_set_mass
#print axioms modulo_set_mass_le

end AspisRowDensity.Generic
end
