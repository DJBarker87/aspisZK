import F3K_CheckpointPreparedFields
set_option autoImplicit false
namespace AspisR1.F3Q_Variant
open AspisR1CurrentCaller.InstalledPreparation

theorem source (out : AspisR1PublicPreparation.verifier.Prepared)
    (same : (Tx1Q_Carriers.prepared (currentPrepared out)).variant=.S2) : out.variant=.S2 := by
  change Tx1Q_Carriers.variant (currentVariant out.variant)=.S2 at same
  cases h : out.variant <;> simp only [h,currentVariant,Tx1Q_Carriers.variant] at same
  all_goals first | cases same | rfl

#print axioms source
end AspisR1.F3Q_Variant
