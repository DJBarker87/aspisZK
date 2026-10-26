import ART_PartialProgram
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_QueryAgreement
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open ART_PartialProgram

/-- Every partial execution is covered on its queried-success cylinder,
including a final failed or diverging syscall. No returns-only certificate. -/
theorem compatible {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (before : Log)
    (agrees : ARS_QueryTransport.Agrees H (run hashv code before).2) :
    Compatible hashv H code := by
  induction code generalizing before with
  | done value => trivial
  | step result next ih =>
    cases result with
    | ok value => exact ih value before agrees
    | fail error => trivial
    | div => trivial
  | read parts next ih =>
    cases answer : hashv parts with
    | fail error => simp only [Compatible,answer]
    | div => simp only [Compatible,answer]
    | ok digest =>
      have member : (⟨parts,ok digest⟩ : Query) ∈
          (run hashv (.read parts next) before).2 := by
        simp only [run,answer]
        obtain ⟨suffix,layout⟩ := prefix_preserved hashv (next digest) (before ++ [⟨parts,ok digest⟩])
        rw [layout]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
      have value := agrees _ member digest rfl
      simp only [Compatible,answer]
      exact ⟨value,ih digest (before ++ [⟨parts,ok digest⟩])
        (by simpa only [run,answer] using agrees)⟩

#print axioms compatible
end AspisR1.ART_QueryAgreement
end
