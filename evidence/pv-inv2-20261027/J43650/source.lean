import R1Z.PV_Inv_RegistryPacking
set_option autoImplicit false
namespace R1Z.PV_Inv_RegistryZeroEvent
open R0P R0Z.HonestValidity PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_GlobalSafety
variable {K W : Type} [Field K] [Zero W] [DecidableEq W]

def zeroEvent (chi : K) (s : State Key K W) : Prop :=
  ∃ key v, v ∈ PV_Inv_RawInvoke.reached (s key) ∧ chi - v = 0

theorem contained (banks : Banks K) (t : Trace K) (join : P_banks banks t)
    (lambda chi : K) (weight : SourceLink K → W) (registry : List (SourceLink K))
    (enumeration : P_registry registry) (s : State Key K W)
    (run : PV_Inv_GlobalSlots.run (empty 0) (entries banks lambda weight registry)=some s) :
    zeroEvent chi s → ¬ NoPole t lambda chi := by
  rintro ⟨key,v,hv,hz⟩ safe
  exact PV_Inv_RegistryPacking.reached_nonzero banks t join lambda chi weight registry enumeration safe s run key v hv hz

#print axioms contained
end R1Z.PV_Inv_RegistryZeroEvent
