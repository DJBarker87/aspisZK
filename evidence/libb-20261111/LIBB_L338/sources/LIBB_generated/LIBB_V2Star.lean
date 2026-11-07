import LIBB_V2Lib
import LIBB_Tx2AuthGate
set_option autoImplicit false
noncomputable section
namespace LIBB_V2Star
open RSL LIBB_ReturnFunctional
/-- Admitted V0-star: the original concrete source bundle, unchanged. -/
abbrev library : TX2_241.V2Lib := LIBB_V2Lib.library
abbrev values : NND_Tx2Values.Values library := LIBB_V2Lib.values

theorem gate (x : Bytes × Bytes × Bytes) (_domain : TX2_241.Dom064 library x) :
 ReturnFunctional (library.tx2auth x.1 x.2.1 x.2.2) :=
 LIBB_Tx2AuthGate.returnFunctional _ _ _

theorem returns (pub proof ck : Bytes) (env : Env) :
 NND_Returned.Returns (library.tx2auth pub proof ck) env (values.auth pub proof ck env) :=
 LIBB_Tx2Auth.returns pub proof ck env

theorem writeFree (pub proof ck : Bytes) : TAS.WriteFree (library.tx2auth pub proof ck) :=
 LIBB_Tx2Auth.writeFree pub proof ck

theorem exact_bundle : library=LIBB_V2Lib.library := rfl
/-- The SAME V0, Root0 and law are used by canonical TAS consumers. -/
theorem canonical_identity : TAS.lib library library.Root0 library.tx2auth=library := rfl

abbrev weak {Ambient X : Type}
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient) : TX2_241.V2Lib :=
 TAS.lib library (fun _ _=>True) (NNC_ObservedLaw.w H d hash world)

theorem weak_identity {Ambient X : Type}
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient) :
 weak H d hash world=TCK.weaken library (NNC_ObservedLaw.w H d hash world) := rfl

theorem weak_exact {Ambient X : Type}
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient) :
 (weak H d hash world).tx2auth=NNC_ObservedLaw.w H d hash world := rfl

#print axioms gate
#print axioms returns
#print axioms writeFree
#print axioms exact_bundle
#print axioms canonical_identity
#print axioms weak_identity
#print axioms weak_exact
end LIBB_V2Star
end
