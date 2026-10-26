import SCE_Execution
import OracleProgramReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_AccountReplay
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment

/-- A cylinder of the full adaptive execution, not merely its first submission. -/
def Consistent {X : Type} (program : Program Bytes State X)
    (native H : Bytes → State) : Prop :=
  ∀ address ∈ (eval native program).1.map Prod.fst, H address = native address

/-- Includes choice queries and all prefixes of rejecting outcomes. -/
theorem replay {X : Type} (program : Program Bytes State X)
    (native H : Bytes → State) (consistent : Consistent program native H) :
    eval H program = eval native program :=
  OracleProgramReplay.eval_eq_of_agrees program native H consistent

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (native H : Bytes → State)
    (consistent : Consistent (account c hashv copy allocator id a) native H)

include consistent
/-- Every predicate of the SAME complete run transports. This permits bank
witnesses fixed by the actual execution; it creates no bank witness from nothing. -/
theorem supported (bankSupported : List (Bytes × State) × GExq_AccountExperiment.Outcome A → Prop)
    (original : bankSupported (eval native (account c hashv copy allocator id a))) :
    bankSupported (eval H (account c hashv copy allocator id a)) := by
  rw [replay _ native H consistent]
  exact original

/-- Pointwise identity preserves arbitrary original outcome and cost laws.
No averaging over a new conditioned distribution is claimed. -/
theorem law {V : Type} (observe : List (Bytes × State) × GExq_AccountExperiment.Outcome A → V) :
    observe (eval H (account c hashv copy allocator id a)) =
      observe (eval native (account c hashv copy allocator id a)) :=
  congrArg observe (replay _ native H consistent)

/-- The runtime recorder executes no extra verifier. -/
theorem runtime :
    eval H (SCE_Experiment.runtime c hashv copy allocator id a) =
      eval native (SCE_Experiment.runtime c hashv copy allocator id a) := by
  rw [runtime_eval,runtime_eval,replay _ native H consistent]

/-- Original first buffers are retained under the same execution identity. -/
theorem first : (eval H a.first).2 = (eval native a.first).2 := by
  have same := congrArg (fun x => x.2.1) (replay _ native H consistent)
  simpa only [first_projection] using same

#print axioms replay
#print axioms supported
#print axioms law
#print axioms runtime
#print axioms first
end AspisR1.ARS_AccountReplay
end
