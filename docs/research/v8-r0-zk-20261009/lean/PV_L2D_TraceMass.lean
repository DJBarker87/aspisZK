import PV_L2D_ExpanderTrace
import PV_L2B_SamplerLaw
set_option autoImplicit false
namespace PV_L2D_TraceMass
open PV_L2D_ScalarRender PV_L2D_ExpanderTrace PV_L2B_SamplerLaw
variable {F : Type} [AddCommGroup F] [Fintype F]

def acceptedTrace (retry : Nat) (c : Clock) (r : Nat) := render tick wordTrace (r+1) retry c true
def failedTrace (retry n : Nat) (c : Clock) := render tick wordTrace n retry c false

theorem translate_at_count (q : ℚ) (w : F) (retry r : Nat) (c : Clock)
    (test : F → List (PV_L2D_ScalarPort.Event PV_L2D_ExpanderPort.WordEvent) → ℚ) :
    (∑ a : F, (geom q r/(Fintype.card F : ℚ))*test (a+w) (acceptedTrace retry c r)) =
      ∑ a : F, (geom q r/(Fintype.card F : ℚ))*test a (acceptedTrace retry c r) := by
  exact Equiv.sum_comp (Equiv.addRight w)
    (fun a => (geom q r/(Fintype.card F : ℚ))*test a (acceptedTrace retry c r))
#print axioms translate_at_count

/-- The count/trace remains joint with the masked value, and the failed
prefix has its own unchanged test. This is the IID kernel law; no statement
here identifies SHA outputs with that kernel or changes the old bad event. -/
def expectation (q : ℚ) (n retry : Nat) (c : Clock) (w : F)
    (test : F → List (PV_L2D_ScalarPort.Event PV_L2D_ExpanderPort.WordEvent) → ℚ)
    (failure : List (PV_L2D_ScalarPort.Event PV_L2D_ExpanderPort.WordEvent) → ℚ) : ℚ :=
  (∑ r ∈ Finset.range n,
    ∑ a : F, (geom q r/(Fintype.card F : ℚ))*test (a+w) (acceptedTrace retry c r)) +
      q^n*failure (failedTrace retry n c)

theorem translated_capped (q : ℚ) (n retry : Nat) (c : Clock) (w : F)
    (test : F → List (PV_L2D_ScalarPort.Event PV_L2D_ExpanderPort.WordEvent) → ℚ)
    (failure : List (PV_L2D_ScalarPort.Event PV_L2D_ExpanderPort.WordEvent) → ℚ) :
    expectation q n retry c w test failure=expectation q n retry c 0 test failure := by
  unfold expectation
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  simpa using translate_at_count q w retry r c test
#print axioms translated_capped

theorem geom_sum (q : ℚ) (n : Nat) :
    (∑ r ∈ Finset.range n, geom q r)=1-q^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih];simp only [geom,pow_succ];ring
#print axioms geom_sum

theorem count_value_normalized (q : ℚ) (r : Nat) :
    (∑ _a : F, geom q r/(Fintype.card F : ℚ))=geom q r := by
  letI : Nonempty F := ⟨0⟩
  have hn : (Fintype.card F : ℚ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp
#print axioms count_value_normalized

theorem complete_mass (q : ℚ) (n : Nat) :
    (∑ r ∈ Finset.range n, ∑ _a : F, geom q r/(Fintype.card F : ℚ)) + q^n=1 := by
  simp only [count_value_normalized,geom_sum]
  ring
#print axioms complete_mass
end PV_L2D_TraceMass
