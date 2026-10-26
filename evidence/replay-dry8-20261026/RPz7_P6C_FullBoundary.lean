import RPz7_P6C_Issued
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_FullBoundary
open Aeneas Aeneas.Std Result SdkC_Source S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation MultiproofConePhysicalTransport

def firstLog {F C : Type} (c : Configuration F C) (hashv : Parts → Result Digest) (f : FirstCut) : Log :=
  (run hashv (P6C_Whole.firstCode c hashv f) []).2

def secondLog {F C : Type} (c : Configuration F C) (hashv : Parts → Result Digest) (s : SecondCut) : Log :=
  (run hashv (P6C_Whole.secondCode c hashv s) []).2

def Facts {F C : Type} (c : Configuration F C) (hashv : Parts → Result Digest)
    (H : Bytes → State) (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut) : Prop :=
  P6C_Whole.SafePair c hashv H saved f s ∧
  P6C_Issued.Boundary hashv H (firstLog c hashv f) ∧
  P6C_Issued.Boundary hashv H (secondLog c hashv s) ∧
  ∀ q ∈ firstLog c hashv f ++ secondLog c hashv s,
    ∀ self, (sdk c).op43 self q.parts = ok (rawOracle H q.parts)

/-- The success-conditioned P6 oracle law for every actually issued call of
both complete installed source programs, directly from the original cuts. -/
theorem same_cuts {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : Parts → Result Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s) :
    Facts c hashv H saved f s := by
  have safe := P6C_Whole.same_cuts c native1 native2 hashv extraction sha256 H p1 syscall
    accounts1 accounts2 saved f s cuts
  have first := P6C_Issued.derive hashv sha256 H p1 syscall
    (P6C_Whole.firstCode c hashv f) (.Ok saved) safe.1.1.1
  have second := P6C_Issued.derive hashv sha256 H p1 syscall
    (P6C_Whole.secondCode c hashv s) (.Ok ()) safe.2.1.1
  refine ⟨safe,first,second,?_⟩
  intro q member
  rcases List.mem_append.mp member with left | right
  · exact P6C_Issued.installed _ native1 native2 hashv extraction H _ first q left
  · exact P6C_Issued.installed _ native1 native2 hashv extraction H _ second q right

#print axioms same_cuts
end AspisR1.P6C_FullBoundary
end
