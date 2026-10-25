import DrvI_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvI_SourceCounterexample
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortRuntimeBindingC7

/-- Total counterinstance: independent of malformed bytes and decoder errors. -/
theorem silent_driver (adapter : AdapterRw.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (i : OraclePortStoredExperimentC4.Input) :
    Port1_Driver.rust adapter DrvI_Counterexample.silent D hash i = .done false := by
  unfold Port1_Driver.rust
  split <;> try rfl
  split <;> first | exact DrvI_Counterexample.silent_stages _ _ _ _ _ | rfl

/-- Success-conditioned separation from ANY accepting source, on the SAME
input and oracle. No claim that a deployed accepting run has been inhabited. -/
theorem accepting_source_differs (adapter : AdapterRw.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (source : Verifier) (i : OraclePortStoredExperimentC4.Input) (H : Bytes → State)
    (accepted : (eval H (source i)).2 = true) :
    source i ≠ Port1_Driver.rust adapter DrvI_Counterexample.silent D hash i := by
  rw [silent_driver]
  intro equal
  rw [equal] at accepted
  cases accepted

/-- Physical holds for the counterinstance, so Physical alone cannot repair
identification with an accepting deployed source. -/
theorem physical_counterinstance (adapter : AdapterRw.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port1_StoredCarrier.Physical (Port1_Driver.rust adapter DrvI_Counterexample.silent D hash) :=
  Port1_StoredCarrier.driver_physical adapter DrvI_Counterexample.silent D hash

#print axioms silent_driver
#print axioms accepting_source_differs
#print axioms physical_counterinstance
end AspisR1.DrvI_SourceCounterexample
end
