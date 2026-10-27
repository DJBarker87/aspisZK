import F3U_Oracle
set_option autoImplicit false
namespace AspisR1.F3U_OracleSeparation
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem same_on_return (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (H1 H2 : Bytes → State)
    (first : S2W_ExtractionBoundary.RuntimeSyscall hashv H1)
    (second : S2W_ExtractionBoundary.RuntimeSyscall hashv H2)
    (parts : SdkC_Source.Parts) (digest : SdkC_Source.Digest) (returned : hashv parts=ok digest) :
    H1 (flatten parts)=H2 (flatten parts) :=
  (first.returningValue parts digest returned).symm.trans (second.returningValue parts digest returned)

theorem cannot_fix_oracle (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (H1 H2 : Bytes → State) (parts : SdkC_Source.Parts) (digest : SdkC_Source.Digest)
    (returned : hashv parts=ok digest) (different : H1 (flatten parts)≠H2 (flatten parts)) :
    ¬ (S2W_ExtractionBoundary.RuntimeSyscall hashv H1 ∧ S2W_ExtractionBoundary.RuntimeSyscall hashv H2) := by
  rintro ⟨first,second⟩
  exact different (same_on_return hashv H1 H2 first second parts digest returned)

#print axioms same_on_return
#print axioms cannot_fix_oracle
end AspisR1.F3U_OracleSeparation
