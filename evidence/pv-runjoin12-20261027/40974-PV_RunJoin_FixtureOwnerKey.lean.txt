import R1Z.PV_RunJoin_FixtureHashCell0

/-! Mathematical fixture owner-key value. The permutation certificate is
composed by named rounds; no concrete hash recurrence is normalized here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P PV_RunJoin_FixtureRecords

theorem owner_init : absorb (spongeInit (0x41530001 : Scalar) 8) (digest 10) = s_0_0 := by
  funext i
  fin_cases i <;> rfl

theorem owner_key : ownerKey (digest 10 : Fin 8 → Scalar) = digestOf s_0_23 := by
  unfold ownerKey spongeStep
  rw [owner_init,permutation_0]

#print axioms owner_init
#print axioms owner_key
end R1Z.PV_RunJoin_FixtureHashModel
