import R1Z.PV_Inv_PoleMass
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_ChargeRules
open R0Z.FsAbort R0Z.HvzkV

theorem already_charged {C : Type} [Fintype C] (zero old : C → Prop) (bound : ℚ)
    (subset : ∀ c, zero c → old c) (charged : eventMass old ≤ bound) : eventMass zero ≤ bound :=
  (eventMass_mono zero old subset).trans charged

theorem no_double_charge {C : Type} [Fintype C] (zero old : C → Prop)
    (subset : ∀ c, zero c → old c) : eventMass (fun c => old c ∨ zero c)=eventMass old := by
  congr 1
  funext c
  exact propext ⟨fun h => h.elim id (subset c),Or.inl⟩

#print axioms already_charged
#print axioms no_double_charge
end R1Z.PV_Inv_ChargeRules
