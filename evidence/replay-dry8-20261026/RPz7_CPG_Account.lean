import RPz7_F3T_AccountSource
import RPz7_F3T_ConditionalSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPG_Account
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : S2W_D189Wrappers.Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (GExq_AccountExperiment.FirstInputs A))
    (chooseSecond : GExq_AccountExperiment.FirstInputs A → alloc.vec.Vec U8 →
      Heap (Nat → Record) → A → Program Bytes State (GExq_AccountExperiment.SecondInputs A))

def source : Program Bytes State (GExq_AccountExperiment.Outcome A) :=
  GExq_AccountExperiment.program c.adapter c.currentBase c.stageBase c.finish
    c.reserved c.query c.geometry c.boundaries c.std hashv copy allocator id adversary chooseSecond

variable (D : LiteralByteProtocol.Decoder) (P : F3T_ByteCarrier.ByteProver) (Q0 Q1 : Nat)
    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : F3T_Runtime.Runtime)
    (raw : F3T_CanonicalJoin.AcceptedVerifierJoin c D (F3T_Installed.source c hashv))
    (binding : F3T_Runtime.StoredCarrierBinding c D (F3T_Installed.source c hashv) P runtime)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)

include queries raw binding prefixBound choiceBound

/-- Retains the account collision mass, charged ONCE, on the actual adaptive
account-entry source experiment. The theorem bounds a sum of the stated masses;
it does not invent identification with an unspecified deployed failure event. -/
theorem bound :
    F3T_RuntimeBound.failureModel runtime +
      F3T_AccountCharge.mass (source c hashv copy allocator id adversary chooseSecond) project select (Q0+Q1) ≤
      F3T_Numeric.total (Q0+Q1) := by
  exact F3T_ConditionalSum.bound c D P (Q0+Q1) queries hashv runtime raw binding
    (source c hashv copy allocator id adversary chooseSecond) project select
    (RawJ_CollisionBudget.first_reads c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std hashv copy allocator id adversary chooseSecond
      Q0 Q1 prefixBound choiceBound)

theorem zero (zeroQueries : Q0+Q1 = 0) :
    F3T_RuntimeBound.failureModel runtime +
      F3T_AccountCharge.mass (source c hashv copy allocator id adversary chooseSecond) project select (Q0+Q1) <
      1/(2:Rat)^100 := by
  have total := bound c hashv copy allocator id adversary chooseSecond D P Q0 Q1 queries
    runtime raw binding prefixBound choiceBound project select
  rw [zeroQueries] at total ⊢
  exact total.trans_lt F3T_Numeric.zero_queries

#print axioms bound
#print axioms zero
end AspisR1.CPG_Account
end
