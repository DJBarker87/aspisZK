import Port9OR_Installed
import OracleProgramLawExt

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_BatchLaw
open FS AspisV8PairedCommitment
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.OracleFiniteSupport

/-- The full physical op5 has ONE fixed lazy-sampling law. Native source
interpretation occurs only pointwise inside its finite-support integrand.
No accepted-only conditioning or whole security-event transport is asserted. -/
theorem batch_lazy {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize) (which : Usize)
    (f : View Bytes State (Result (core.result.Result Unit VTop_Stages.verifier.Error)) → ℚ) :
    let program := Port9OR_Installed.batch D hash proof p folded which
    let s := support program
    lazyMean program emptyTable f = mean (fun H : {a // a ∈ s} → State =>
      let oracle := extend s H default
      f (CheckpointBytes5Inputs.observe (Port9OR_Code.trace
        (VTop_Checkpoint.digest (Port9OR_Bodies.native D oracle)) hash
        (Port9OR_Installed.code D hash proof p folded which)).1,
        Port4B_Install.batch (Port9OR_Bodies.native D oracle) proof p folded which hash)) := by
  dsimp only
  have law := finite_support_oracle_law (Port9OR_Installed.batch D hash proof p folded which)
    (support (Port9OR_Installed.batch D hash proof p folded which)) (fun _ h => h) (default : State) f
  apply law.symm.trans
  apply mean_congr
  intro H
  rw [Port9OR_Installed.effects]

#print axioms batch_lazy
end AspisR1.Port9OR_BatchLaw
end
