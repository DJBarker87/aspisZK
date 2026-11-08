import NNH_CorrectConfiguration
import NNH_HostEnv
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_PreflightDigest
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- An allowed non-returning syscall; no runtime totality is in D188/P1. -/
def divergent : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest := fun _ => .div

theorem divergent_runtime (sha : Bytes → State) :
 S2W_ExtractionBoundary.RuntimeSyscall divergent sha := by
 constructor
 intro parts digest returned
 cases returned

theorem reflexive_p1 (sha : Bytes → State) :
 S2W_ExtractionBoundary.P1 sha sha := ⟨fun _ => rfl⟩

/-- Exact P2 obligation at one slot: it requires equality of the COMPLETE
syscall reply, while RuntimeSyscall only constrains a returned digest value. -/
theorem digestSource_at_iff
 (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE)
 (reserve : NP6_StdModel.Reservation)
 (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
 (parts : S2Z.Oracle.Parts) :
 ((NNH_CorrectConfiguration.sdk missing env err reserve).op43 () parts =
   S2W_DigestExtraction.digest hashv () parts) ↔
 hashv parts = LIB_Env.hashv env parts := by
 rw [S2W_DigestExtraction.digest_eq_hashv]
 change LIB_Env.hashv env parts = hashv parts ↔ _
 exact eq_comm

/-- P2 fails even with valid P1 and RuntimeSyscall. This is independent of
all seven-account buffers, adversary choice, success and Root0. -/
theorem digestSource_divergent
 (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE)
 (reserve : NP6_StdModel.Reservation) (parts : S2Z.Oracle.Parts) :
 (NNH_CorrectConfiguration.sdk missing env err reserve).op43 () parts ≠
 S2W_DigestExtraction.digest divergent () parts := by
 rw [S2W_DigestExtraction.digest_eq_hashv]
 change Result.ok _ ≠ Result.div
 intro impossible
 cases impossible

#print axioms divergent_runtime
#print axioms reflexive_p1
#print axioms digestSource_at_iff
#print axioms digestSource_divergent
end AspisR1.NNH_PreflightDigest
