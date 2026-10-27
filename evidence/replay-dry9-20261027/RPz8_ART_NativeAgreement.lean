import RPz8_ART_Coverage
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_NativeAgreement
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem issued {A : Type} (hashv : Parts → Result Digest) (native : Bytes → State)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native) (code : Code A) :
    ARS_QueryTransport.Agrees native (run hashv code []).2 := by
  intro q member digest returned
  have associated := SdkC_Source.associated hashv code [] (by simp) q member
  exact syscall.returningValue q.parts digest (associated.symm.trans returned)

#print axioms issued
end AspisR1.ART_NativeAgreement
end
