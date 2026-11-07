import NNG_InstallBase
import LIB_VCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBDigest
open Aeneas Aeneas.Std NNG_verify_finish

/-- Runtime reply and byte partitions are transported unchanged. This does
not compute or unfold SHA; the value remains the existing Env oracle. -/
def digest (env : RSL.Env) : aspis_core.digest.Digest32 Unit :=
  ⟨(LIB_VCode.digest env).coremarkerCopyInst,(LIB_VCode.digest env).digest⟩

theorem installed (env : RSL.Env) : NNG_Install.digest (digest env) = LIB_VCode.digest env := rfl
#print axioms installed

theorem reply (env : RSL.Env) (parts : Slice (Slice U8)) :
    (digest env).digest () parts =
      .ok (LIB_Env.nativeKey (env.sha256 (NNC_ResumeEvents.parts parts))) :=
  LIB_VCode.digest_exact env parts
#print axioms reply
end AspisR1.NNG_LIBDigest
