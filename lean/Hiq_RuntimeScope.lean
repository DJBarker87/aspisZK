import Hiq_CanonicalAccountDriver
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_RuntimeScope
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7
open Aeneas Aeneas.Std

/-- A checked interface obstruction at the installed driver, NOT a shipped
source/runtime execution or a security counterexample. Carried and identical
physical bytes cannot constrain a still-arbitrary runtime's chronological log. -/
theorem carried_insufficient {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : Prover) (pub proof : Slice U8) (state : State) :
    ∃ (runtime : Runtime) (run : RunView), runtime = .done (some run) ∧
      run.2.1 = Hiq_CanonicalCarrier.input pub proof ∧ run.2.2 = true ∧
      Port1_StoredCarrier.Carried run.2.1 ∧
      ¬ StoredCarrierBinding D (DrvC_Implementation.driver c) P runtime := by
  let i := Hiq_CanonicalCarrier.input pub proof
  let r0 : RunView := ([],i,true)
  let r1 : RunView := ([([],state)],i,true)
  by_cases h0 : StoredCarrierBinding D (DrvC_Implementation.driver c) P (.done (some r0))
  · refine ⟨.done (some r1),r1,rfl,rfl,rfl,Hiq_CanonicalCarrier.carried _ _,?_⟩
    intro h1
    have e0 := h0 (fun _ => state) r0 rfl rfl
    have e1 := h1 (fun _ => state) r1 rfl rfl
    have logs := congrArg (fun r : RunView => r.1.length) (e0.trans e1.symm)
    change 0 = 1 at logs
    exact Nat.noConfusion logs
  · exact ⟨.done (some r0),r0,rfl,rfl,rfl,Hiq_CanonicalCarrier.carried _ _,h0⟩

#print axioms carried_insufficient
end AspisR1.Hiq_RuntimeScope
end
