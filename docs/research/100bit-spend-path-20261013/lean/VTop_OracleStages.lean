import VTop_OracleCode
import VTop_Flow

/-! Named external-body joins for the actual extracted stage call sites.
Library/constants are a separate explicit port. These laws are hypotheses,
not claims that existing cone certificates already instantiate the ports. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_OracleStages
open Aeneas Aeneas.Std Result VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def OperationJoin (source model : Implementation) (id : Nat) : Prop :=
  ∀ {A : Type} (call : Call A), operationId call = id →
    ∀ (H : Bytes → State) (value : A), (eval H (source call)).2 = .ok value →
      eval H (source call) = eval H (model call)

def libraryIds : List Nat := [0,1,2,13,14,15,16,20,21,22,23,24]

structure ConeJoins (source model : Implementation) : Prop where
  shape : OperationJoin source model 3
  scan : OperationJoin source model 4
  batch : OperationJoin source model 5
  query : OperationJoin source model 6
  prepare : OperationJoin source model 7
  writer : OperationJoin source model 8
  flush : OperationJoin source model 9
  pending : OperationJoin source model 10
  geometry : OperationJoin source model 11
  initial : OperationJoin source model 12
  powers : OperationJoin source model 17
  reader : OperationJoin source model 18
  finish : OperationJoin source model 19
  library : ∀ {A : Type} (call : Call A), operationId call ∈ libraryIds →
    ∀ (H : Bytes → State) (value : A), (eval H (source call)).2 = .ok value →
      eval H (source call) = eval H (model call)

theorem all_calls (source model : Implementation) (joins : ConeJoins source model) :
    CallJoin source model := by
  intro A call H value accepted
  cases call <;> first
  | exact joins.shape _ rfl H value accepted
  | exact joins.scan _ rfl H value accepted
  | exact joins.batch _ rfl H value accepted
  | exact joins.query _ rfl H value accepted
  | exact joins.prepare _ rfl H value accepted
  | exact joins.writer _ rfl H value accepted
  | exact joins.flush _ rfl H value accepted
  | exact joins.pending _ rfl H value accepted
  | exact joins.geometry _ rfl H value accepted
  | exact joins.initial _ rfl H value accepted
  | exact joins.powers _ rfl H value accepted
  | exact joins.reader _ rfl H value accepted
  | exact joins.finish _ rfl H value accepted
  | exact joins.library _ (by simp [operationId, libraryIds]) H value accepted

theorem accepted_tx1 (source model : Implementation) (joins : ConeJoins source model)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (saved : alloc.vec.Vec U8) (H : Bytes → State)
    (accepted : (eval H (interpret source
      (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof split hash none))).2 = .ok (.Ok saved)) :
    eval H (interpret source (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof split hash none)) =
      eval H (interpret model (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof split hash none)) :=
  accepted_interpret_eq source model (all_calls source model joins) _ H _ accepted

theorem accepted_tx2_common (source model : Implementation) (joins : ConeJoins source model)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (H : Bytes → State)
    (accepted : (eval H (interpret source
      (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof checkpoint hash none))).2 = .ok (.Ok ())) :
    eval H (interpret source (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof checkpoint hash none)) =
      eval H (interpret model (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof checkpoint hash none)) :=
  accepted_interpret_eq source model (all_calls source model joins) _ H _ accepted

theorem accepted_tx2_authenticated (source model : Implementation) (joins : ConeJoins source model)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (H : Bytes → State)
    (accepted : (eval H (interpret source
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash none))).2 = .ok (.Ok ())) :
    eval H (interpret source (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash none)) =
      eval H (interpret model (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash none)) :=
  accepted_interpret_eq source model (all_calls source model joins) _ H _ accepted

#print axioms all_calls
#print axioms accepted_tx1
#print axioms accepted_tx2_common
#print axioms accepted_tx2_authenticated
end AspisR1.VTop_OracleStages
end
