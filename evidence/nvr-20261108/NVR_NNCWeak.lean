import NVR_CandidateRoots
import NNC_G1a
-- NVR_ provenance: copied from evidence/stage-wrap-20261111/NMV_NNCWeak.lean (research, sha256 2c4477bd06454d0f...).
-- Change: NMV_ -> NVR_ renames of the rev4-repaired chain modules only; no proof edit.
-- Needs Aeneas and the NNC_G1a stack; not compiled locally.
set_option autoImplicit false
noncomputable section
namespace NVR_NNCWeak
open RSL
open Aeneas Aeneas.Std AspisR1 VTop_Stages NLW_Full064
open AspisV8R19.SourceDuplexStep (State)

/-- Install the NNC write-free native-outcome law factory, retaining its
explicit complete trace renderer. No empty renderer or native064 transport
is manufactured here. The child parameter is the FULL weak241 RowSpec. -/
theorem weak240 {Ambient X : Type} (L : PoolLib) (D : DeployedIds)
 (debug : verifier.Error → String) (root0 : Bytes → Bytes → Prop)
 (auth : Bytes → Bytes → Bytes → Spec (Except verifier.Error Unit))
 (H : AspisV8R19.DuplexFrames.Bytes → State)
 (digest : aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient) (render : NNC_WriteFree.Renderer Ambient X H)
 (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D
  (TCK.weaken (NNC_G1a.base debug root0 auth) (NNC_WriteFree.law H digest hash world render)) child)
 (a : TX2_240.Args) (s : SdkState) (env : Env) :
 TX2_240.Ref L D
  (TCK.weaken (NNC_G1a.base debug root0 auth) (NNC_WriteFree.law H digest hash world render))
  a s env (NMV_ConcreteWindows.stage2 allocation child a s env) :=
 NVR_CandidateRoots.root240 L D _ allocation child packet a s env
  (TCK.domain240_weaken _ _ a s)

/-- Actual weak-law specialization of the complete G2 reference frame.
Library effect laws stay explicit; arbitrary PoolLib operations may write. -/
theorem frame {Ambient X : Type} (L : PoolLib) (D : DeployedIds)
 (pl : NMV_NoWrite.PoolLaws L)
 (debug : verifier.Error → String) (root0 : Bytes → Bytes → Prop)
 (auth : Bytes → Bytes → Bytes → Spec (Except verifier.Error Unit))
 (H : AspisV8R19.DuplexFrames.Bytes → State)
 (digest : aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient) (render : NNC_WriteFree.Renderer Ambient X H)
 (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D
  (TCK.weaken (NNC_G1a.base debug root0 auth) (NNC_WriteFree.law H digest hash world render)) child)
 (a : TX2_240.Args) (s : SdkState) (env : Env) :
 TAS.Frame s (NMV_ConcreteWindows.stage2 allocation child a s env) :=
 NVR_G2Reference.frame L D (NNC_G1a.base debug root0 auth) pl
  (NNC_WriteFree.law H digest hash world render)
  (NNC_WriteFree.writeFree H digest hash world render) a s env _
  (weak240 L D debug root0 auth H digest hash world render allocation child packet a s env)

/-- Returned full SDK-cell and token frame; no stopped post-state. -/
theorem sdk {Ambient X : Type} (L : PoolLib) (D : DeployedIds)
 (debug : verifier.Error → String) (root0 : Bytes → Bytes → Prop)
 (auth : Bytes → Bytes → Bytes → Spec (Except verifier.Error Unit))
 (H : AspisV8R19.DuplexFrames.Bytes → State)
 (digest : aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient) (render : NNC_WriteFree.Renderer Ambient X H)
 (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D
  (TCK.weaken (NNC_G1a.base debug root0 auth) (NNC_WriteFree.law H digest hash world render)) child)
 (a : TX2_240.Args) (s t : SdkState) (env : Env)
 (r : Except ProgramError Unit) (events : List Event)
 (returned : NMV_ConcreteWindows.stage2 allocation child a s env = ⟨.ret (r,t),events⟩) :
 t.cells=s.cells ∧ t.next=s.next+(if TX2_240.badRoute a then 0 else 7) := by
 have h := weak240 L D debug root0 auth H digest hash world render allocation child packet a s env
 rw [returned] at h
 exact NMV_G2State.reference_sdk L D _ a s t env r events h

#print axioms weak240
#print axioms frame
#print axioms sdk
end NVR_NNCWeak
