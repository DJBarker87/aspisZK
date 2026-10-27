import R1Z.PV_Inv_EntryReference
import R1Z.PV_Inv_ActiveRegistry
import R1Z.PV_Inv_RegistryNoPole
set_option autoImplicit false
namespace R1Z.PV_Inv_EntrySafety
open R0P R0Z.HonestValidity PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference
variable {K W : Type} [Field K]
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

theorem producer (banks : Banks K) (t : Trace K) (join : P_banks banks t)
    (lambda chi : K) (weight : SourceLink K → W) (registry : List (SourceLink K))
    (enumeration : P_registry registry) (safe : NoPole t lambda chi)
    (l : SourceLink K) (hl : l ∈ registry) :
    chi ≠ (PV_Inv_EntryReference.producer banks lambda weight l).2.value := by
  obtain ⟨model,hm,he⟩ := PV_Inv_RegistryInput.member registry enumeration l hl
  subst l
  change chi ≠ PV_Inv_BankCompression.producer banks lambda (ofModel model)
  rw [PV_Inv_BankCompression.producer_equation banks t join lambda model]
  exact PV_Inv_RegistryNoPole.producer t lambda chi model hm (PV_Inv_ActiveRegistry.active model hm).1 safe

theorem consumer (banks : Banks K) (t : Trace K) (join : P_banks banks t)
    (lambda chi : K) (weight : SourceLink K → W) (registry : List (SourceLink K))
    (enumeration : P_registry registry) (safe : NoPole t lambda chi)
    (l : SourceLink K) (hl : l ∈ registry) :
    chi ≠ (PV_Inv_EntryReference.consumer banks lambda weight l).2.value := by
  obtain ⟨model,hm,he⟩ := PV_Inv_RegistryInput.member registry enumeration l hl
  subst l
  change chi ≠ PV_Inv_BankCompression.consumer banks lambda (ofModel model)
  rw [PV_Inv_BankCompression.consumer_equation banks t join lambda model]
  exact PV_Inv_RegistryNoPole.consumer t lambda chi model hm (PV_Inv_ActiveRegistry.active model hm).2 safe

#print axioms producer
#print axioms consumer
end R1Z.PV_Inv_EntrySafety
