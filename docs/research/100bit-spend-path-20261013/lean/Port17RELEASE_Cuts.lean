import Port17RELEASE_TX1
import Port17RELEASE_TX2
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port17RELEASE_Cuts
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port17RELEASE_Domain Port16CUT_Cuts
theorem sourceOne_bound (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : ReleaseBudgets rest w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State) :
    (eval H (sourceOne (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash semantic pub proof)).1.length ≤ oneWeight w := by
  have h : (eval H (sourceOne (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash semantic pub proof)).1.length ≤ (Port15DRIVER_TX1.sites w).sum := by
    exact Eq.mp (congrArg (fun p : Program Bytes State
      (Result (core.result.Result (alloc.vec.Vec U8) verifier.Error)) =>
        (eval H p).1.length ≤ (Port15DRIVER_TX1.sites w).sum)
      (sourceOne_eq (Port9OR_Installed.implementation ops reserved unwrap rest)
        D hash semantic pub proof).symm)
      (Port17RELEASE_TX1.tx1 ops reserved unwrap rest w budgets D hash semantic pub proof H)
  exact Nat.le_trans h (one_sum w)

theorem sourceTwo_bound (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : ReleaseBudgets rest w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (H : Bytes → State) :
    (eval H (sourceTwo (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash pub proof checkpoint)).1.length ≤ twoWeight w := by
  have h : (eval H (sourceTwo (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash pub proof checkpoint)).1.length ≤ (Port16CUT_TX2.sites w).sum := by
    exact Eq.mp (congrArg (fun p : Program Bytes State
      (Result (core.result.Result Unit verifier.Error)) =>
        (eval H p).1.length ≤ (Port16CUT_TX2.sites w).sum)
      (sourceTwo_eq (Port9OR_Installed.implementation ops reserved unwrap rest)
        D hash pub proof checkpoint).symm)
      (Port17RELEASE_TX2.tx2 ops reserved unwrap rest w budgets D hash pub proof checkpoint H)
  exact Nat.le_trans h (two_sum w)


#print axioms sourceOne_bound
#print axioms sourceTwo_bound
end AspisR1.Port17RELEASE_Cuts
end
