import ARR_OracleCoverage
import ARR_WorldCompatibility
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_ReturnCoverage
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

def ReturnsOnly (log : SdkC_Source.Log) : Prop :=
  ∀ q ∈ log, ∃ digest, q.returned = .ok digest

theorem of_returns {A : Type} (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (compatible : ARR_WorldCompatibility.Compatible H hashv)
    (code : Code A) (before : SdkC_Source.Log)
    (safe : ReturnsOnly (SdkC_Source.run hashv code before).2) :
    ARR_OracleCoverage.Covered H hashv code := by
  induction code generalizing before with
  | done x => trivial
  | step r k ih =>
    cases r with
    | ok x => exact ih x before safe
    | fail e => trivial
    | div => trivial
  | read parts k ih =>
    cases answer : hashv parts with
    | ok digest =>
      have decoded := compatible parts digest answer
      have encoded : encodeState (H (flatten parts)) = digest := by
        rw [← decoded]
        exact array_roundtrip digest
      have next := ih digest (before ++ [⟨parts,.ok digest⟩])
        (by simpa only [SdkC_Source.run,answer] using safe)
      exact ⟨answer.trans (congrArg Result.ok encoded.symm),by rw [encoded]; exact next⟩
    | fail error =>
      have bad : (⟨parts,.fail error⟩ : SdkC_Source.Query) ∈
          (SdkC_Source.run hashv (.read parts k) before).2 := by
        simp only [SdkC_Source.run,answer]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      obtain ⟨digest,impossible⟩ := safe _ bad
      cases impossible
    | div =>
      have bad : (⟨parts,.div⟩ : SdkC_Source.Query) ∈
          (SdkC_Source.run hashv (.read parts k) before).2 := by
        simp only [SdkC_Source.run,answer]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      obtain ⟨digest,impossible⟩ := safe _ bad
      cases impossible

theorem returns_of_covered {A : Type} (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : Code A) (covered : ARR_OracleCoverage.Covered H hashv code)
    (before : SdkC_Source.Log) (initial : ReturnsOnly before) :
    ReturnsOnly (SdkC_Source.run hashv code before).2 := by
  induction code generalizing before with
  | done x => exact initial
  | step r k ih =>
    cases r with
    | ok x => exact ih x covered before initial
    | fail e => exact initial
    | div => exact initial
  | read parts k ih =>
    obtain ⟨answer,next⟩ := covered
    simp only [SdkC_Source.run,answer]
    apply ih _ next
    intro q member
    rcases List.mem_append.mp member with old | fresh
    · exact initial q old
    · obtain rfl := List.mem_singleton.mp fresh
      exact ⟨_,rfl⟩

/-- Under the RETAINED returning-value interface, exact reached-read coverage
is equivalent to all attempted syscalls returning successfully. Pure source
errors are included in this class. Native syscall errors/divergence are exactly
what this certificate excludes; no upstream bank exclusion is asserted. -/
theorem iff_returns {A : Type} (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (compatible : ARR_WorldCompatibility.Compatible H hashv) (code : Code A) :
    ARR_OracleCoverage.Covered H hashv code ↔
      ReturnsOnly (SdkC_Source.run hashv code []).2 := by
  constructor
  · intro covered
    exact returns_of_covered H hashv code covered [] (by intro q member; cases member)
  · exact of_returns H hashv compatible code []

#print axioms of_returns
#print axioms returns_of_covered
#print axioms iff_returns
end AspisR1.ARR_ReturnCoverage
end
