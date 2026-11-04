import R1Z.PV_RunJoin_FixtureHashCell4
import R1Z.PV_RunJoin_FixtureHashCell5

/-! Exact mathematical nullifier for the shared input fixture. No native
compiler or selected/deployed public statement is installed by this lemma. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P PV_RunJoin_FixtureRecords

theorem nullifier_init : absorb (spongeInit (0x41530002 : Scalar) 16) (digest 10) = s_4_0 := by
  funext i
  fin_cases i <;> rfl

theorem nullifier_absorb : absorb s_4_23 (digest 100) = s_5_0 := by
  funext i
  fin_cases i <;> rfl

theorem nullifier : nullifierHash (digest 10 : Fin 8 → Scalar) (digest 100) = digestOf s_5_23 := by
  unfold nullifierHash spongeStep
  rw [nullifier_init,permutation_4,nullifier_absorb,permutation_5]

#print axioms nullifier_init
#print axioms nullifier_absorb
#print axioms nullifier
end R1Z.PV_RunJoin_FixtureHashModel
