import R1Z.PV_Inv_EntriesSafety
import R1Z.PV_Inv_GlobalOrigin
set_option autoImplicit false
namespace R1Z.PV_Inv_RegistryPacking
open R0P R0Z.HonestValidity PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_GlobalSafety
variable {K W : Type} [Field K] [Zero W] [DecidableEq W]

theorem reached_nonzero (banks : Banks K) (t : Trace K) (join : P_banks banks t)
    (lambda chi : K) (weight : SourceLink K → W) (registry : List (SourceLink K))
    (enumeration : P_registry registry) (safe : NoPole t lambda chi)
    (s : State Key K W) (run : PV_Inv_GlobalSlots.run (empty 0) (entries banks lambda weight registry)=some s)
    (key : Key) (v : K) (reached : v ∈ PV_Inv_RawInvoke.reached (s key)) : chi - v ≠ 0 := by
  obtain ⟨e,he,_,hv⟩ := PV_Inv_GlobalOrigin.origin 0 _ s run key v reached
  rw [←hv]
  exact sub_ne_zero.mpr (PV_Inv_EntriesSafety.all_entries banks t join lambda chi weight registry enumeration safe e he)

#print axioms reached_nonzero
end R1Z.PV_Inv_RegistryPacking
