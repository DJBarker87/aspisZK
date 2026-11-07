import NMX_Semantics
set_option autoImplicit false
noncomputable section
namespace NMX_DenoteStep
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel

theorem call {A : Type} (owners : Owners) (lane : NMX_RawChildren.LaneNative)
 (registry : NMX_RawChildren.RegistryNative) (cmd : Command A) (next : A → Program Auth) :
 NMX_Semantics.denote owners lane registry
  (NMX_Program.bind (NMX_SourceProgram.call cmd) next) =
 RSL.RS.bind (NMX_Semantics.command owners lane registry cmd)
  (fun value => NMX_Semantics.denote owners lane registry (next value)) := rfl

theorem raw_ok {A : Type} (owners : Owners) (lane : NMX_RawChildren.LaneNative)
 (registry : NMX_RawChildren.RegistryNative) (value : A) (next : A → Program Auth) :
 NMX_Semantics.denote owners lane registry
  (NMX_Program.bind (NMX_SourceProgram.raw (.ok value)) next) =
 NMX_Semantics.denote owners lane registry (next value) := by
 unfold NMX_SourceProgram.raw
 rw [call]
 exact RSL.RS.bind_pure value _

theorem check (owners : Owners) (lane : NMX_RawChildren.LaneNative)
 (registry : NMX_RawChildren.RegistryNative) (bad : Bool) (next : Unit → Program Auth) :
 NMX_Semantics.denote owners lane registry
  (NMX_Program.bind (NMX_SourceProgram.check bad) next) =
 if bad then RSL.RS.throw .invalidAccountData
 else NMX_Semantics.denote owners lane registry (next ()) := by
 cases bad <;> rfl
#print axioms call
#print axioms raw_ok
#print axioms check
end NMX_DenoteStep
end
