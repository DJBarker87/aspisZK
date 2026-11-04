import NGC_DigestRef.Funs
import NGC_Initialization
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_DigestBridge
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- NCO-pinned extracted observation reference. The syscall reply is arbitrary;
this theorem makes no claim about the SHA256 value. -/
theorem observed (parts : Slice (Slice U8)) (reply : Array U8 32#usize) :
 NGC_DigestRef.digest_ref parts reply=ok reply := rfl
/-- Concrete source-fission interpretation: hashv supplies an array and the
wrapper returns that SAME complete array at that SAME ordered parts slice. -/
def backend (hashv : Slice (Slice U8)→Array U8 32#usize) : aspis_core.digest.Digest32 Unit where
 coremarkerCopyInst := {cloneInst:={clone:=fun value=>ok value}}
 digest := fun _ parts=>NGC_DigestRef.digest_ref parts (hashv parts)
theorem forwarding (hashv : Slice (Slice U8)→Array U8 32#usize) (parts : Slice (Slice U8)) :
 (backend hashv).digest () parts=ok (hashv parts) := rfl
/-- This is the existing runtime digest-value trust row, explicitly retained.
The forwarding certificate neither supplies nor weakens it. -/
def RuntimeSha256Realization (hashv : Slice (Slice U8)→Array U8 32#usize)
 (H : AspisV8R19.DuplexFrames.Bytes→AspisV8R19.SourceDuplexStep.State) : Prop :=
 ∀ parts,CheckpointBytesDigest.stateOf (hashv parts)=H (AspisR1DigestLogCarrier.flatten parts)
theorem checkpoint_oracle (hashv : Slice (Slice U8)→Array U8 32#usize)
 (H : AspisV8R19.DuplexFrames.Bytes→AspisV8R19.SourceDuplexStep.State)
 (runtime : RuntimeSha256Realization hashv H) :
 CheckpointBytes5Inputs.Oracle (backend hashv) () H := by
 intro parts digest call
 have same := Result.ok.inj call
 subst digest
 exact runtime parts
#print axioms observed
#print axioms forwarding
#print axioms checkpoint_oracle
end AspisR1.NGC_DigestBridge
end
