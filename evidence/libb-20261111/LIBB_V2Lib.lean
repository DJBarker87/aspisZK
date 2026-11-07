import LIBB_Tx2Auth
import NND_Tx2Values
import NNC_ObservedLaw
set_option autoImplicit false
noncomputable section
namespace LIBB_V2Lib
open RSL
/-- Concrete V0 source bundle. Whole-observation Functional for this full
stopped-prefix law is not asserted; see LIBB_REMAINING.md's gate boundary. -/
def library : TX2_241.V2Lib :=
 ⟨LIBB_V2Carriers.VErr,LIBB_V2Carriers.debug,LIBB_V2Carriers.Root0,LIBB_Tx2Auth.law⟩

def values : NND_Tx2Values.Values library where
 auth := LIBB_Tx2Auth.value
 auth_ret := fun p q r env _=>LIBB_Tx2Auth.returns p q r env

theorem error_exact : library.VErr=LIB_ErrorDebug.VErr := rfl
theorem debug_exact : library.debug=LIB_ErrorDebug.debug := rfl
theorem root0_exact : library.Root0=LIB_Root0.root0 := rfl
theorem auth_exact : library.tx2auth=LIBB_Tx2Auth.law := rfl

theorem domain_exact (pub proof ck : Bytes) :
 TX2_241.Dom064 library (pub,proof,ck) ↔ LIBB_Tx2Domain.domain pub proof ck := Iff.rfl

theorem returned_gate (pub proof ck : Bytes) (env : Env)
 (_domain : TX2_241.Dom064 library (pub,proof,ck)) :
 NND_Returned.Returns (library.tx2auth pub proof ck) env (values.auth pub proof ck env) ∧
 Spec.Functional (LIBB_Tx2Auth.resolved pub proof ck) :=
 ⟨LIBB_Tx2Auth.returns pub proof ck env,LIBB_Tx2Auth.resolved_functional pub proof ck⟩

/-- Unchanged NNC weak law registered on exactly this V0. Runtime binders
belong to the host; no native execution or renderer is selected here. -/
def weak {Ambient X : Type} (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient) : TX2_241.V2Lib :=
 TAS.lib library (fun _ _=>True) (NNC_ObservedLaw.w H d hash world)

theorem weak_exact {Ambient X : Type}
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X) (world : NLM_PacketTypes.World Ambient) :
 (weak H d hash world).tx2auth=NNC_ObservedLaw.w H d hash world := rfl

theorem weak_same_error {Ambient X : Type}
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X) (world : NLM_PacketTypes.World Ambient) :
 (weak H d hash world).VErr=library.VErr ∧
 (weak H d hash world).debug=library.debug := ⟨rfl,rfl⟩

theorem canonical_identity : TAS.lib library library.Root0 library.tx2auth=library := rfl

theorem weak_identity {Ambient X : Type}
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X) (world : NLM_PacketTypes.World Ambient) :
 weak H d hash world=TCK.weaken library (NNC_ObservedLaw.w H d hash world) := rfl

#print axioms error_exact
#print axioms debug_exact
#print axioms root0_exact
#print axioms auth_exact
#print axioms domain_exact
#print axioms returned_gate
#print axioms weak_exact
#print axioms weak_same_error
#print axioms canonical_identity
#print axioms weak_identity
end LIBB_V2Lib
end
