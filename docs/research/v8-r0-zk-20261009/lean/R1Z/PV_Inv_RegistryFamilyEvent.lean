import R1Z.PV_Inv_RegistryZeroEvent
set_option autoImplicit false
namespace R1Z.PV_Inv_RegistryFamilyEvent
open R0P R0Z.HonestValidity PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference
open PV_Inv_GlobalSlots PV_Inv_GlobalSafety
variable {K W : Type} [Field K] [Zero W] [DecidableEq W]

/-- All row-builder inputs and all reached helper slots at once. No charge
is multiplied by the number of registry links, slots, rows or helper calls. -/
def event (t : Trace K) (lambda chi : K) : Prop :=
  ∃ banks : Banks K, P_banks banks t ∧ ∃ registry : List (SourceLink K), P_registry registry ∧
  ∃ weight : SourceLink K → W, ∃ s : State Key K W,
    PV_Inv_GlobalSlots.run (empty 0) (entries banks lambda weight registry)=some s ∧
    PV_Inv_RegistryZeroEvent.zeroEvent chi s

theorem contained (t : Trace K) (lambda chi : K) : event (W := W) t lambda chi → ¬ NoPole t lambda chi := by
  rintro ⟨banks,hb,registry,hr,weight,s,hs,hz⟩
  exact PV_Inv_RegistryZeroEvent.contained banks t hb lambda chi weight registry hr s hs hz

#print axioms contained
end R1Z.PV_Inv_RegistryFamilyEvent
