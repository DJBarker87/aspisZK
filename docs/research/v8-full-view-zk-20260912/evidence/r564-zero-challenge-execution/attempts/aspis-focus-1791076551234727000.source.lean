import AspisV8R19.R551FirstFourZeroBlockV10
import AspisV8R19.R170LimbSamplerExecution
import AspisV8R19.R167TranscriptPrimitiveExecution
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R564ZeroChallengeExecutionV2
open Aeneas Aeneas.Std Result ControlFlow
open DuplexFrames SourceDuplexStep SamplerWords
open QM31SamplerProgram

theorem limb_run_first_zero (H : Bytes → State) (c : Cursor)
    (hidx : c.index.val < 4)
    (hz : masked 31 (word c.block ⟨c.index.val, by have hi := c.index.isLt; omega⟩) = 0) :
    limbRun H 8 c =
      ([], (some 0, ⟨c.state, c.block,
        ⟨c.index.val + 1, by have hi := c.index.isLt; omega⟩⟩)) := by
  have hn : c.index.val ≠ 8 := by omega
  have hr : readRun H c =
      ([], (word c.block ⟨c.index.val, by have hi := c.index.isLt; omega⟩,
        ⟨c.state, c.block, ⟨c.index.val + 1, by have hi := c.index.isLt; omega⟩⟩)) := by
    simp [readRun, hn]
  rw [limbRun, hr]
  have hreject : ¬ masked 31 (word c.block ⟨c.index.val, by have hi := c.index.isLt; omega⟩) = 2147483647 := by
    rw [hz]
    norm_num
  simp only [hz, if_neg hreject, List.nil_append]

theorem limbs_run_four_zero (H : Bytes → State) (state block : State)
    (hz : ∀ j : Fin 4, masked 31 (word block ⟨j.val, by omega⟩) = 0) :
    limbsRun H 4 ⟨state, block, 0⟩ = ([], (some [0, 0, 0, 0], ⟨state, block, 4⟩)) := by
  have l0 : limbRun H 8 ⟨state, block, 0⟩ = ([], (some 0, ⟨state, block, 1⟩)) := by
    simpa using limb_run_first_zero H ⟨state, block, 0⟩ (by decide) (by simpa using hz 0)
  have l1 : limbRun H 8 ⟨state, block, 1⟩ = ([], (some 0, ⟨state, block, 2⟩)) := by
    simpa using limb_run_first_zero H ⟨state, block, 1⟩ (by decide) (by simpa using hz 1)
  have l2 : limbRun H 8 ⟨state, block, 2⟩ = ([], (some 0, ⟨state, block, 3⟩)) := by
    simpa using limb_run_first_zero H ⟨state, block, 2⟩ (by decide) (by simpa using hz 2)
  have l3 : limbRun H 8 ⟨state, block, 3⟩ = ([], (some 0, ⟨state, block, 4⟩)) := by
    simpa using limb_run_first_zero H ⟨state, block, 3⟩ (by decide) (by simpa using hz 3)
  rw [limbsRun]
  simp only [l0]
  rw [limbsRun]
  simp only [l1]
  rw [limbsRun]
  simp only [l2]
  rw [limbsRun]
  simp only [l3]
  simp

theorem challengeRun_firstFourZero (H : Bytes → State) (s : State)
    (hz : ∀ j : Fin 4,
      masked 31 (word (SourceDuplexStep.step H s).1 ⟨j.val, by omega⟩) = 0) :
    challengeRun H s =
      (SourceDuplexStep.calls H s, (some [0, 0, 0, 0], (SourceDuplexStep.step H s).2)) := by
  unfold challengeRun
  dsimp only
  let p := SourceDuplexStep.step H s
  have hp : limbsRun H 4 ⟨p.2, p.1, 0⟩ = ([], (some [0, 0, 0, 0], ⟨p.2, p.1, 4⟩)) := by
    apply limbs_run_four_zero
    intro j
    simpa [p] using hz j
  simp [p, hp]

theorem challenge_source_firstFourZero (H : DuplexFrames.Bytes → SourceDuplexStep.State)
    (s : SourceDuplexStep.State)
    (hz : ∀ j : Fin 4,
      masked 31 (word (SourceDuplexStep.step H s).1 ⟨j.val, by omega⟩) = 0) :
    transcript.Transcript.challenge_qm31
        (R167TranscriptPrimitiveExecution.transcriptFor H s) =
      .ok (R170LimbSamplerExecution.encodeResult (some [0, 0, 0, 0]),
        R167TranscriptPrimitiveExecution.transcriptFor H (SourceDuplexStep.step H s).2) := by
  rw [R170LimbSamplerExecution.challenge_exact, challengeRun_firstFourZero H s hz]
  rfl

#print axioms limb_run_first_zero
#print axioms limbs_run_four_zero
#print axioms challengeRun_firstFourZero
#print axioms challenge_source_firstFourZero
end AspisV8R19.R564ZeroChallengeExecutionV2
