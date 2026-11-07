import LIBB_PartitionEnv
import LIB_Root0
import NMN_064
set_option autoImplicit false
noncomputable section
namespace LIBB_Tx2Domain
open Aeneas Aeneas.Std AspisR1 VTop_Stages
/-- Literal transcription of the four existing NMN own-input clauses. -/
def domain (publicBytes proof checkpoint : RSL.Bytes) : Prop :=
 proof.length=57607 ∧ checkpoint.length=1768 ∧ publicBytes.length≤1880 ∧
 LIB_Root0.root0 checkpoint proof

theorem native (env : RSL.Env) (publicBytes proof checkpoint : Slice U8) :
 domain (LIB_Carriers.bytes publicBytes) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes checkpoint) ↔
 NMN_064.Domain (⟨LIBB_PartitionEnv.digest env,publicBytes,proof,checkpoint,()⟩ : NLW_Full064.Args Unit) := by
 constructor
 · rintro ⟨hp,hc,hu,hr⟩
   exact ⟨by simpa only [LIB_Carriers.bytes,NNC_ByteCarriers.host,List.length_map] using hp,
    by simpa only [LIB_Carriers.bytes,NNC_ByteCarriers.host,List.length_map] using hc,
    by simpa only [LIB_Carriers.bytes,NNC_ByteCarriers.host,List.length_map] using hu,
    (LIB_Root0.exact checkpoint proof).mp hr⟩
 · intro h
   exact ⟨by simpa only [LIB_Carriers.bytes,NNC_ByteCarriers.host,List.length_map] using h.proofExtent,
    by simpa only [LIB_Carriers.bytes,NNC_ByteCarriers.host,List.length_map] using h.checkpointExtent,
    by simpa only [LIB_Carriers.bytes,NNC_ByteCarriers.host,List.length_map] using h.publicBound,
    (LIB_Root0.exact checkpoint proof).mpr h.root0⟩
#print axioms native
end LIBB_Tx2Domain
end
