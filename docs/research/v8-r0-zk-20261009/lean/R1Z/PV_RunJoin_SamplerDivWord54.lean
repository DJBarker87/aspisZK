import R1Z.PV_RunJoin_CircleRawSampler52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerDivWord54

def prime : U64 := UScalar.cast .U64 PV_RunJoin_CircleRawTower52.field.P
theorem complete (x : U64) : ∃ q r, x/prime=ok q ∧ x%prime=ok r ∧ r.val<2147483647 := by
  have positive : prime.val≠0 := by decide
  obtain ⟨q,hq,hqv⟩ := UScalar.div_spec x (y:=prime) positive
  obtain ⟨r,hr,hrv⟩ := WP.spec_imp_exists (UScalar.rem_spec x (y:=prime) positive)
  refine ⟨q,r,hq,hr,?_⟩
  rw [hrv]
  exact Nat.mod_lt _ (by decide)
#print axioms prime
#print axioms complete
end R1Z.PV_RunJoin_SamplerDivWord54
