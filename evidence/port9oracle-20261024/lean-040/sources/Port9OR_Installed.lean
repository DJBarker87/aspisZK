import Port9OR_Batch
import Port9OR_Bodies

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Installed
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def code {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (which : Usize) :
    CheckpointBytes5Effect.Code (core.result.Result Unit verifier.Error) := do
  let out ← Port9OR_Batch.code Port4B_Install.leaves (VTop_Checkpoint.digest D) hash proof p folded which
  pure (match out with | .Ok a => .Ok a | .Err e => .Err (Port3_CheckpointInstall.error e))

def batch {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (which : Usize) :=
  Port9OR_Code.program (VTop_Checkpoint.digest D) hash (code D hash proof p folded which)

/-- The physical source definition is fixed independently of Parsed/q/nodes.
Its source return is instantiated pointwise, not installed using H. -/
theorem value {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (which : Usize)
    (H : Bytes → State) :
    (eval H (batch D hash proof p folded which)).2=
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded which hash := by
  rw [batch,Port9OR_Code.value]
  simp only [code,CheckpointBytes5Effect.erase_bind,CheckpointBytes5Effect.erase_pure,Port9OR_Batch.source]
  rfl

/-- Complete source observation, including duplicate hash-before-compare,
count/padding rejection and prefixes before outer errors. -/
theorem effects {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (which : Usize)
    (H : Bytes → State) :
    eval H (batch D hash proof p folded which)=
      (CheckpointBytes5Inputs.observe (Port9OR_Code.trace
        (VTop_Checkpoint.digest (Port9OR_Bodies.native D H)) hash (code D hash proof p folded which)).1,
        Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded which hash) := by
  apply Prod.ext
  · have h := congrArg Prod.fst (Port9OR_Code.correspondence (VTop_Checkpoint.digest D) hash
      (code D hash proof p folded which) H)
    exact h
  · exact value D hash proof p folded which H

def other (rest : VTop_OracleCode.Implementation) : VTop_OracleCode.Implementation := fun call =>
  match call with
  | .op5 D proof p folded which hash => batch D hash proof p folded which
  | call => rest call

def implementation (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : VTop_OracleCode.Implementation) : VTop_OracleCode.Implementation :=
  Port9OR_Bodies.implementation ops reserved unwrap (other rest)

theorem installed (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : VTop_OracleCode.Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (which : Usize) :
    implementation ops reserved unwrap rest (.op5 D proof p folded which hash)=batch D hash proof p folded which := rfl

#print axioms value
#print axioms effects
#print axioms installed
end AspisR1.Port9OR_Installed
end
