import Port1_Library
import AdapterRwModel

/-! Natural two-stage source lift on the actual extracted carriers. Decode
uses adapter op47, validation op21 and the extracted semantic-public getter.
The physical source reads stored/public bytes; its preparation body owns its
transcript effects. A separate logical proof field is not a Rust argument.
This module deliberately does not claim the frozen2 model-order identity. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_Driver
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7
abbrev Semantic := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public

def asSlice (bytes : Bytes) : Option (Slice U8) :=
  if h : bytes.length ≤ Usize.max then
    some ⟨bytes.map (fun b => (UScalar.ofNatCore b.val b.isLt : U8)), by simpa using h⟩
  else none

/-- Complete success/error selection at the extracted decoder/validator cuts.
Their concrete implementations remain their existing source ports. -/
def decodeSemantic (adapter : AdapterRw.Ops) (pub : Slice U8) : Result (Option Semantic) := do
  let decoded ← adapter.op47 pub
  match decoded with
  | .Err _ => .ok none
  | .Ok statement =>
    let checked ← adapter.op21 statement
    match checked with
    | .Err _ => .ok none
    | .Ok () =>
      let semantic ← AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement
      .ok (some semantic)

def verdict (result : Result (core.result.Result Unit verifier.Error)) : Bool :=
  match result with | .ok (.Ok ()) => true | _ => false

/-- TX2 consumes precisely the checkpoint returned by this TX1, with the same
public/proof slices and None observer in both calls. -/
def stages (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (semantic : Semantic)
    (pub proof : Slice U8) : Program Bytes State Bool :=
  bind (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))
    fun first => match first with
    | .ok (.Ok saved) =>
      bind (interpret impl (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof saved.deref hash none))
        fun second => .done (verdict second)
    | _ => .done false

/-- Explicit headline-typed lift, with no invented logical-proof reads.
This remains a source interpretation under the supplied body/decoder ports,
not a deployed account/runtime binding. -/
def rust (adapter : AdapterRw.Ops) (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) : Verifier := fun i =>
  match asSlice i.statement.pubBytes, asSlice i.stored with
  | some pub, some proof =>
    match decodeSemantic adapter pub with
    | .ok (some semantic) => stages impl D hash semantic pub proof
    | _ => .done false
  | _, _ => .done false

/-- Source/model stage substitution now composes both entries with the same
returned checkpoint, rather than independent stage runs. -/
theorem stages_substitute (source model : Implementation)
    (joins : VTop_OracleStages.ConeJoins source model) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (semantic : Semantic)
    (pub proof : Slice U8) (H : Bytes → State)
    (accepted : (eval H (stages source D hash semantic pub proof)).2 = true) :
    eval H (stages source D hash semantic pub proof) =
      eval H (stages model D hash semantic pub proof) := by
  unfold stages at accepted ⊢
  simp only [eval_bind] at accepted ⊢
  cases first : (eval H (interpret source
    (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2 with
  | fail e => simp only [first, eval, Bool.false_eq_true] at accepted
  | div => simp only [first, eval, Bool.false_eq_true] at accepted
  | ok result =>
    cases result with
    | Err e => simp only [first, eval, Bool.false_eq_true] at accepted
    | Ok saved =>
      have one := VTop_OracleStages.accepted_tx1 source model joins D hash semantic pub proof 10#usize saved H first
      rw [← one]
      simp only [first] at accepted ⊢
      simp only [eval_bind, eval, List.append_nil] at accepted ⊢
      cases second : (eval H (interpret source
        (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof saved.deref hash none))).2 with
      | fail e => simp only [second, verdict, Bool.false_eq_true] at accepted
      | div => simp only [second, verdict, Bool.false_eq_true] at accepted
      | ok result =>
        cases result with
        | Err e => simp only [second, verdict, Bool.false_eq_true] at accepted
        | Ok unit =>
          cases unit
          have two := VTop_OracleStages.accepted_tx2_authenticated source model joins D hash pub proof saved.deref H second
          rw [← two, second]

#print axioms decodeSemantic
#print axioms stages_substitute
end AspisR1.Port1_Driver
end
