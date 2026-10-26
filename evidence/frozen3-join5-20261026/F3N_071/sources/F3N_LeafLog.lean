import F3N_SourceEffect
import Port4B_LeafCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_LeafLog
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem accepted (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (kind : Usize) (opening : Slice U8) (length : opening.val.length=832)
    (digest : SdkC_Source.Digest)
    (success : (SdkC_Source.run hashv (Port4B_LeafCode.code kind opening) []).1=ok digest) :
    decodeState digest=H (flatten (Port4B_LeafCode.input kind opening)) ∧
    SdkC_Source.readLog (SdkC_Source.run hashv (Port4B_LeafCode.code kind opening) []).2=
      [(flatten (Port4B_LeafCode.input kind opening),H (flatten (Port4B_LeafCode.input kind opening)))] := by
  have source := (SdkC_Source.erasure hashv (Port4B_LeafCode.code kind opening) []).symm.trans success
  have exactCode := Port4B_LeafCode.code_exact (SdkC_Source.dictionary hashv) () kind opening length []
  have returned : hashv (Port4B_LeafCode.input kind opening)=ok digest := exactCode.1.symm.trans source
  have value := (syscall.returningValue _ digest returned).trans (p1.realization _)
  obtain ⟨after,ran,logs⟩ := F3N_SourceEffect.accepted hashv (Port4B_LeafCode.code kind opening)
    digest [] [] rfl success
  rw [exactCode.2] at ran
  change (do let d ← hashv (Port4B_LeafCode.input kind opening);ok (d,[]++[(_,d)]))=ok (digest,after) at ran
  rw [returned] at ran
  have same : [(Port4B_LeafCode.input kind opening,digest)]=after := congrArg Prod.snd (Result.ok.inj ran)
  refine ⟨value,?_⟩
  rw [← logs,← same]
  simp only [CheckpointBytes5Inputs.observe,List.map_cons,List.map_nil,value]

#print axioms accepted
end AspisR1.F3N_LeafLog
end
