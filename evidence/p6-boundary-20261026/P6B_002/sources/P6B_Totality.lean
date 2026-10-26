import S2W_DigestExtraction

set_option autoImplicit false
noncomputable section
namespace AspisR1.P6B_Totality
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open S2W_DigestExtraction

/-- The exact extra obligation is return/termination, not digest correctness. -/
def Returns (hashv : Parts → Result Digest) : Prop :=
  ∀ parts, ∃ digest, hashv parts = ok digest

/-- Success-only RuntimeSyscall and P1 give total equality precisely when
all calls return. Neither failure nor divergence is removed by the wrapper. -/
theorem wrapper_total_iff (hashv : Parts → Result Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (runtime : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (self : AdapterRw.SolanaDigest) :
    (∀ parts, digest hashv self parts =
      ok (MultiproofConePhysicalTransport.rawOracle H parts)) ↔ Returns hashv := by
  simp only [digest_eq_hashv]
  constructor
  · intro total parts
    exact ⟨_,total parts⟩
  · intro returns parts
    obtain ⟨value,returned⟩ := returns parts
    have decoded := (runtime.returningValue parts value returned).trans (p1.realization _)
    have encoded : value = MultiproofConePhysicalTransport.rawOracle H parts := by
      change value = encodeState (H (flatten parts))
      rw [← decoded]
      exact (array_roundtrip value).symm
    exact returned.trans (congrArg Result.ok encoded)

/-- D188 preserves the same necessary and sufficient runtime obligation. -/
theorem installed_total_iff (ops : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : Parts → Result Digest) (extraction : AeneasExtraction ops native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (runtime : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (self : AdapterRw.SolanaDigest) :
    (∀ parts, ops.op43 self parts =
      ok (MultiproofConePhysicalTransport.rawOracle H parts)) ↔ Returns hashv := by
  simp only [extraction.digestSource]
  exact wrapper_total_iff hashv sha256 H p1 runtime self

/-- A partial syscall with genuine successful calls: zero-part queries return,
nonempty queries diverge. This is an interface model, not deployed behaviour. -/
def partialHash (H : Bytes → State) (parts : Parts) : Result Digest :=
  if parts.val = [] then ok (MultiproofConePhysicalTransport.rawOracle H parts) else .div

def emptyParts : Parts := ⟨[],by simp⟩
def onePart : Parts := ⟨[⟨[],by simp⟩],by simp; scalar_tac⟩

theorem partial_runtime (H : Bytes → State) :
    S2W_ExtractionBoundary.RuntimeSyscall (partialHash H) H := by
  constructor
  intro parts value returned
  unfold partialHash at returned
  split at returned
  · cases returned
    exact state_roundtrip _
  · cases returned

theorem partial_success (H : Bytes → State) :
    partialHash H emptyParts = ok (MultiproofConePhysicalTransport.rawOracle H emptyParts) := by
  simp only [partialHash,emptyParts,ite_true]

theorem partial_not_total (H : Bytes → State) : ¬ Returns (partialHash H) := by
  intro returns
  obtain ⟨value,returned⟩ := returns onePart
  simp only [partialHash,onePart,List.cons_ne_nil,if_false] at returned
  cases returned

/-- Both existing runtime premises are satisfiable with successful queries,
while totality fails. No new trust item is adopted by this countermodel. -/
theorem nonvacuity (H : Bytes → State) :
    S2W_ExtractionBoundary.P1 H H ∧
    S2W_ExtractionBoundary.RuntimeSyscall (partialHash H) H ∧
    (∃ parts value, partialHash H parts = ok value) ∧ ¬ Returns (partialHash H) :=
  ⟨⟨fun _ => rfl⟩,partial_runtime H,⟨emptyParts,_,partial_success H⟩,partial_not_total H⟩

#print axioms wrapper_total_iff
#print axioms installed_total_iff
#print axioms partial_runtime
#print axioms partial_success
#print axioms partial_not_total
#print axioms nonvacuity
end AspisR1.P6B_Totality
end
