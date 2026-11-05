import NGT_FrameChain
import NFW_Transcript
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGT_BlockAssociation
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Bytes32 := Array U8 32#usize

theorem absorb_parts (state : Bytes32) (tag : U8) (payload : Slice U8) :
 NGT_NBA_Transcript.absorbParts state tag payload=NFW_Transcript.absorbParts state tag payload := rfl

theorem read_parts (state : Bytes32) (tag : U8) :
 NGT_NBA_Transcript.readParts state tag=NFW_Transcript.readParts state tag := rfl

/-- Canonical trait transport of the CLOSED runtime wrapper; borrowed parts
and reply are unchanged. Runtime SHA256=H remains the existing trust row. -/
def runtime (hashv : Slice (Slice U8)→Bytes32) : aspis_core.Digest32 Unit where
 coremarkerCopyInst := {cloneInst:={clone:=fun value=>ok value}}
 digest := fun _ parts=>NGC_DigestRef.digest_ref parts (hashv parts)

theorem runtime_forward (hashv : Slice (Slice U8)→Bytes32) (parts : Slice (Slice U8)) :
 (runtime hashv).digest () parts=(NGC_DigestBridge.backend hashv).digest () parts := rfl

/-- Install only the three actual local digest observations. The next state is
constructed from reply three; no arbitrary successful block/scalar equation is
accepted as a premise. Read and advance both use the SAME absorbed reply. -/
def observed {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row tag : U8) (payload : Slice U8) (absorbed value final : Bytes32)
 (tagCall : (160#u8+row : Result U8)=ok tag)
 (first : D.digest before.hash (NFW_Transcript.absorbParts before.state tag payload)=ok absorbed)
 (second : D.digest before.hash (NFW_Transcript.readParts absorbed 1#u8)=ok value)
 (third : D.digest before.hash (NFW_Transcript.readParts absorbed 2#u8)=ok final) :
 NGT_NBL_BlockTrace.Block D before row payload :=
 ⟨tag,tagCall,absorbed,value,final,first,second,third⟩

theorem scalar {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row tag : U8) (payload : Slice U8) (mode : Bool) (absorbed value final : Bytes32)
 (tagCall : (160#u8+row : Result U8)=ok tag)
 (first : D.digest before.hash (NFW_Transcript.absorbParts before.state tag payload)=ok absorbed)
 (second : D.digest before.hash (NFW_Transcript.readParts absorbed 1#u8)=ok value)
 (third : D.digest before.hash (NFW_Transcript.readParts absorbed 2#u8)=ok final)
 (out : aspis_core.field.WideExact) (reduction : NGT_Reduction.Scalar value mode out) :
 PreparedModel.scalar NGT_NBA_Installed.actual.sampling D before row payload mode=
 ok (out,{before with state:=final}) :=
 NGT_SamplerLaw.scalar D before row payload mode
  (observed D before row tag payload absorbed value final tagCall first second third) out reduction

theorem scalar_k {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row tag : U8) (payload : Slice U8) (absorbed value final : Bytes32)
 (tagCall : (160#u8+row : Result U8)=ok tag)
 (first : D.digest before.hash (NFW_Transcript.absorbParts before.state tag payload)=ok absorbed)
 (second : D.digest before.hash (NFW_Transcript.readParts absorbed 1#u8)=ok value)
 (third : D.digest before.hash (NFW_Transcript.readParts absorbed 2#u8)=ok final)
 (out : aspis_core.field.QM31) (reduction : NGT_Reduction.K value out) :
 PreparedModel.scalar_k NGT_NBA_Installed.actual.sampling D before row payload=
 ok (out,{before with state:=final}) :=
 NGT_SamplerLaw.scalar_k D before row payload
  (observed D before row tag payload absorbed value final tagCall first second third) out reduction
#print axioms absorb_parts
#print axioms read_parts
#print axioms runtime_forward
#print axioms scalar
#print axioms scalar_k
end AspisR1.NGT_BlockAssociation
