import R1Z.PV_Inv_PreGuard
import R1Z.PV_Inv_RegistryZeroEvent
set_option autoImplicit false
namespace R1Z.PV_Inv_GuardedRegistry
open R0P PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference
open PV_Inv_GlobalSlots PV_Inv_GlobalSafety
variable {K W : Type} [Field K] [DecidableEq K] [Zero W] [DecidableEq W]

theorem no_zero (banks : Banks K) (t : Trace K) (join : P_banks banks t)
    (lambda chi : K) (weight : SourceLink K → W) (registry : List (SourceLink K))
    (enumeration : P_registry registry) (s : State Key K W)
    (run : PV_Inv_GlobalSlots.run (empty 0) (entries banks lambda weight registry)=some s)
    (guard : PV_Inv_PreGuard.noPoleRef t lambda chi = true) :
    ¬ PV_Inv_RegistryZeroEvent.zeroEvent chi s := by
  intro hz
  exact PV_Inv_RegistryZeroEvent.contained banks t join lambda chi weight registry enumeration s run hz
    ((PV_Inv_PreGuard.source_equation t lambda chi).mp guard)

#print axioms no_zero
end R1Z.PV_Inv_GuardedRegistry
