import NLT_NativeWindows
set_option autoImplicit false
noncomputable section
namespace NLT_RuntimeDigest
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- ONE existing runtime digest realization is shared by C01 and C04. The
root will use this fixed interpretation, not an unrelated free Digest32/Ops
dictionary. Native syscall byte/reply transport remains the retained runtime
trust row and existing CLOSED digest child, never a new SHA implementation. -/
def digest (H : Bytes → State) : VTop_Stages.aspis_core.digest.Digest32 Unit :=
 ⟨(NKV_ConcreteChildren.digest H).coremarkerCopyInst,(NKV_ConcreteChildren.digest H).digest⟩
theorem resume_same (H : Bytes → State) :
 NJC_ResumeCalls.digest (digest H)=NKV_ConcreteChildren.digest H := by
 cases NKV_ConcreteChildren.digest H
 rfl
theorem reply_same (H : Bytes → State) (chunks : Slice (Slice U8)) :
 (digest H).digest () chunks=(NKV_ConcreteChildren.digest H).digest () chunks := rfl
set_option pp.proofs false
#print digest
#print axioms resume_same
#print axioms reply_same
end NLT_RuntimeDigest
