import RPz7_P6C_Whole
import RPz7_P6C_Callbacks
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_Issued
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConePhysicalTransport

/-- Success-conditioned replacement of the old all-input oracle field. The
carrier is the source-computed ordered attempt log, with duplicates retained. -/
def Boundary (hashv : Parts → Result Digest) (H : Bytes → State) (log : Log) : Prop :=
  ∀ q ∈ log,
    q.returned = ok (rawOracle H q.parts) ∧
    hashv q.parts = ok (rawOracle H q.parts) ∧
    S2W_DigestExtraction.digest hashv () q.parts = ok (rawOracle H q.parts) ∧
    run hashv (digestCode q.parts) [] =
      (ok (rawOracle H q.parts),[⟨q.parts,ok (rawOracle H q.parts)⟩])

theorem derive {A : Type} (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (code : Code A) (value : A)
    (accepted : (run hashv code []).1 = ok value) :
    Boundary hashv H (run hashv code []).2 := by
  intro q member
  obtain ⟨digest,returned,actual⟩ := P6C_Accepted.actual_calls_ok hashv code value accepted q member
  have same := (P6C_Extension.agrees hashv H q.parts digest actual).symm.trans
    (P6C_Extension.realization hashv sha256 H p1 syscall q.parts)
  have hash := actual.trans (congrArg Result.ok same)
  refine ⟨returned.trans (congrArg Result.ok same),hash,?_,?_⟩
  · exact (S2W_DigestExtraction.digest_eq_hashv hashv () q.parts).trans hash
  · rw [digest_trace,hash,List.nil_append]

/-- D188 ties every issued source query to the installed SDK wrapper. This
law has the actual Ops and hashv; it does not replace the runtime dictionary. -/
theorem installed (ops : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : Parts → Result Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (H : Bytes → State) (log : Log) (boundary : Boundary hashv H log) :
    ∀ q ∈ log, ∀ self, ops.op43 self q.parts = ok (rawOracle H q.parts) := by
  intro q member self
  rw [extraction.digestSource,S2W_DigestExtraction.digest_eq_hashv]
  exact (boundary q member).2.1

/-- Membership, rather than a universal syscall-return hypothesis, suffices
for the exact parent compression instance at any actually issued address. -/
theorem parent {A : Type} (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (code : Code A) (value : A) (accepted : (run hashv code []).1 = ok value)
    (left right : Digest) (query : Query)
    (issued : query ∈ (run hashv code []).2)
    (address : query.parts = MultiproofConePhysicalDigest.parts left right) :
    run hashv (digestCode (MultiproofConePhysicalDigest.parts left right)) [] =
      (ok (rawOracle H (MultiproofConePhysicalDigest.parts left right)),
        [⟨MultiproofConePhysicalDigest.parts left right,
          ok (rawOracle H (MultiproofConePhysicalDigest.parts left right))⟩]) := by
  have law := (derive hashv sha256 H p1 syscall code value accepted query issued).2.2.2
  simpa only [address] using law

#print axioms derive
#print axioms installed
#print axioms parent
end AspisR1.P6C_Issued
end
