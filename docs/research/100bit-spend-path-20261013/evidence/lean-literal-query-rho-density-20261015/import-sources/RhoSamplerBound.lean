import R1QueryResidualBridge
import R0C.ModuloCounting

/-! Independent-answer density of the explicit modulo-reduction sampler
against the concrete query residual set. Input and output encodings are
equivalences, not assumed uniformity laws. Source byte/field correspondence,
Merkle binding and shared-oracle Fiat--Shamir remain separate obligations. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.RhoSamplerBound

open AspisCircleGroupOrder AspisR1.MatchingSupport
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound

variable {A K E : Type} [Fintype A] [Field K] [Fintype K]
  [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod P) E]

/-- Balanced reduction has at most floor(B/n)+1 inputs per output. Applying
the 21-root count gives this unconditional fresh-answer residual bound. -/
theorem modulo_bad_mass {B n : Nat} (hn : 0 < n)
    (input : A ≃ Fin B) (output : Fin n ≃ K)
    (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) :
    mean (fun a : A => indicator
      (output (R0C.ModuloCounting.reduce hn (input a)) ∈
        AspisR1.QueryResidualBridge.rhoBad iota d q)) ≤
      21 * (((B / n + 1 : Nat) : ℚ) / B) := by
  have hmass := R0C.ModuloCounting.event_mass_le
    (fun a : A => output (R0C.ModuloCounting.reduce hn (input a)))
    (((B / n + 1 : Nat) : ℚ) / B)
    (R0C.ModuloCounting.encoded_mass_le hn input output)
    (AspisR1.QueryResidualBridge.rhoBad iota d q)
  apply hmass.trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast AspisR1.QueryResidualBridge.rhoBad_card iota d q
  · positivity

def rhoCap : ℚ :=
  21 * (((2^256 / P^4 + 1 : Nat) : ℚ) / (2^256 : Nat))

/-- Small closed integer/rational arithmetic only; no field enumeration. -/
theorem rhoCap_lt_two_neg_119 : rhoCap < 1 / (2^119 : ℚ) := by
  norm_num [rhoCap, P]

/-- The actual parameter sizes, with the byte ranking and field ranking
left explicit. This is a theorem about the specified encoded modulo map. -/
theorem qm31_parameter_bad_mass
    (input : A ≃ Fin (2^256)) (output : Fin (P^4) ≃ K)
    (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) :
    mean (fun a : A => indicator
      (output (R0C.ModuloCounting.reduce (by norm_num [P]) (input a)) ∈
        AspisR1.QueryResidualBridge.rhoBad iota d q)) <
      1 / (2^119 : ℚ) :=
  (modulo_bad_mass (by norm_num [P]) input output iota d q).trans_lt
    rhoCap_lt_two_neg_119

#print axioms modulo_bad_mass
#print axioms rhoCap_lt_two_neg_119
#print axioms qm31_parameter_bad_mass

end AspisR1.RhoSamplerBound
end
