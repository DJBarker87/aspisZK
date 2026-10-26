import SCE_AccountBound
import F3T_AccountCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_AccountCollision
open FS FS2
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)

include prefixBound choiceBound

/-- Collision mass for the SAME complete account program, with all rejection
prefixes retained. This is not a source-event refinement or a security bound. -/

theorem collision :
    F3T_AccountCharge.mass (account c hashv copy allocator id a) project select (Q0+Q1) ≤
      F3T_Numeric.accountLoss (Q0+Q1) := by
  apply F3T_AccountCharge.bound
  intro H
  exact (VerifierCallBudget.firstReads_le_length emptyTable _).trans
    (SCE_AccountBound.issued c hashv copy allocator id a Q0 Q1 prefixBound choiceBound H)

#print axioms collision
end AspisR1.SCE_AccountCollision
end
