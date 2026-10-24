import Port17RELEASE_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port17RELEASE_Control
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port17RELEASE_Domain Port16CUT_Cuts
open Port16CUT_Driver (next stages_eq)
theorem next_bound (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : ReleaseBudgets rest w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof : Slice U8) (H : Bytes → State)
    (first : Result (core.result.Result (alloc.vec.Vec U8) verifier.Error)) :
    (eval H (next (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash pub proof first)).1.length ≤ twoWeight w := by
  cases first with
  | fail e => exact Nat.zero_le _
  | div => exact Nat.zero_le _
  | ok result =>
    cases result with
    | Err e => exact Nat.zero_le _
    | Ok saved =>
      change (eval H (bind
        (sourceTwo (Port9OR_Installed.implementation ops reserved unwrap rest) D hash pub proof saved.deref)
        (fun second : Result (core.result.Result Unit verifier.Error) => .done (Port1_Driver.verdict second)))).1.length ≤ twoWeight w
      exact (Port16CUT_Bind.done_tail_length H
        (sourceTwo (Port9OR_Installed.implementation ops reserved unwrap rest) D hash pub proof saved.deref)
        Port1_Driver.verdict).le.trans
        (Port17RELEASE_Cuts.sourceTwo_bound ops reserved unwrap rest w budgets D hash pub proof saved.deref H)

theorem stages (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : ReleaseBudgets rest w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State) :
    (eval H (Port1_Driver.stages (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash semantic pub proof)).1.length ≤ 1046 + delegatedWeight w := by
  have joined := @Port12COUNT_Installed.program_bind_bound
    (Result (core.result.Result (alloc.vec.Vec U8) verifier.Error)) Bool H
    (sourceOne (Port9OR_Installed.implementation ops reserved unwrap rest) D hash semantic pub proof)
    (next (Port9OR_Installed.implementation ops reserved unwrap rest) D hash pub proof)
    (oneWeight w) (twoWeight w)
    (Port17RELEASE_Cuts.sourceOne_bound ops reserved unwrap rest w budgets D hash semantic pub proof H)
    (next_bound ops reserved unwrap rest w budgets D hash pub proof H)
  have target := Eq.mp (congrArg (fun p : Program Bytes State Bool =>
    (eval H p).1.length ≤ oneWeight w + twoWeight w)
    (stages_eq (Port9OR_Installed.implementation ops reserved unwrap rest) D hash semantic pub proof).symm) joined
  exact target.trans (weights w).le

theorem rust (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : ReleaseBudgets rest w)
    (adapter : AdapterRw.Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (i : OraclePortStoredExperimentC4.Input) :
    (eval H (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash i)).1.length ≤ 1046 + delegatedWeight w := by
  unfold Port1_Driver.rust
  repeat' first
    | exact stages ops reserved unwrap rest w budgets D hash _ _ _ H
    | exact Nat.zero_le _
    | (split)


#print axioms next_bound
#print axioms stages
#print axioms rust
end AspisR1.Port17RELEASE_Control
end
