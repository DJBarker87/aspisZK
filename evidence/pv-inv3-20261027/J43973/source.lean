import R1Z.PV_Inv_EntrySafety
set_option autoImplicit false
namespace R1Z.PV_Inv_EntriesSafety
open R0P R0Z.HonestValidity PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference
variable {K W : Type} [Field K]

theorem all_entries (banks : Banks K) (t : Trace K) (join : P_banks banks t)
    (lambda chi : K) (weight : SourceLink K → W) (registry : List (SourceLink K))
    (enumeration : P_registry registry) (safe : NoPole t lambda chi) :
    ∀ e ∈ entries banks lambda weight registry, chi ≠ e.2.value := by
  intro e he
  obtain ⟨l,hl,he⟩ := PV_Inv_EntryReference.member banks lambda weight registry e he
  rcases he with rfl|rfl
  · exact PV_Inv_EntrySafety.producer banks t join lambda chi weight registry enumeration safe l hl
  · exact PV_Inv_EntrySafety.consumer banks t join lambda chi weight registry enumeration safe l hl

#print axioms all_entries
end R1Z.PV_Inv_EntriesSafety
