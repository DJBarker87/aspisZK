import R1Z.PV_Inv_DecodedRun
import R1Z.PV_Inv_MapReached
import R1Z.PV_Inv_RegistryPacking
set_option autoImplicit false
namespace R1Z.PV_Inv_DecodedSafety
open R0P R0Z.HonestValidity PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_MapGlobalStep PV_Inv_GlobalSafety
variable {V K W : Type} [Field K] [Zero W] [DecidableEq W]

theorem reached_nonzero (decode : V → K) (z : V) (zero_join : decode z=0)
    (banks : Banks K) (t : Trace K) (join : P_banks banks t) (lambda chi : K)
    (weight : SourceLink K → W) (registry : List (SourceLink K)) (enumeration : P_registry registry)
    (es : List (Key × Entry V W)) (entry_join : es.map (keyed decode)=entries banks lambda weight registry)
    (s : State Key V W) (run : PV_Inv_GlobalSlots.run (empty z) es=some s)
    (safe : NoPole t lambda chi) (key : Key) (v : V) (hv : v ∈ PV_Inv_RawInvoke.reached (s key)) :
    chi - decode v ≠ 0 := by
  have hr := PV_Inv_DecodedRun.source_equation decode z 0 zero_join es _ entry_join s run
  apply PV_Inv_RegistryPacking.reached_nonzero banks t join lambda chi weight registry enumeration safe
    (state decode s) hr key (decode v)
  change decode v ∈ PV_Inv_RawInvoke.reached (PV_Inv_MapSlots.slots decode (s key))
  rw [PV_Inv_MapReached.reached_map]
  exact List.mem_map.mpr ⟨v,hv,rfl⟩

#print axioms reached_nonzero
end R1Z.PV_Inv_DecodedSafety
