import Port1_LibrarySource
import VTop_OracleStages

/-! Concrete library interpretation for the extracted operation inventory.
The only library trust fields below concern the two pure std methods; all
protocol helpers/constants are installed by their source definitions. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_Library
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- D157/D133 pure Option and Result semantics at candidate.tx1/tx2_common:
Option::ok_or (inactive decode), Result::unwrap (folded-root array conversion).
Neither field mentions a stage return, oracle observation or acceptance. -/
structure TrustedStd (ops : Ops) : Prop where
  option_ok_or : ∀ {T E : Type} (x : Option T) (e : E), ops.op0 x e = Port1_LibrarySource.okOr x e
  result_unwrap32 : ∀ x, ops.unwrap32 x = Port1_LibrarySource.unwrap32 x

/-- Exact source constants and library helper bodies. Body operations remain
unchanged; std semantics are retained as the explicit TrustedStd boundary. -/
def install (ops : Ops) : Ops :=
  { ops with
    op1 := .ok Port1_LibrarySource.zero
    op2 := Port1_LibrarySource.decode
    op13 := Port1_LibrarySource.mark
    op14 := .ok 7783#usize
    op15 := .ok 7751#usize
    op16 := .ok 10#usize
    op20 := .ok 10055#usize
    op21 := .ok 8007#usize
    op22 := .ok 7527#usize
    op23 := .ok 7495#usize }

/-- An explicit inhabiting std dictionary, useful for the substituted model.
This constructor is not an assertion about an arbitrary Ops argument. -/
def std (ops : Ops) : Ops :=
  { ops with op0 := Port1_LibrarySource.okOr, unwrap32 := Port1_LibrarySource.unwrap32 }

theorem std_semantics (ops : Ops) : TrustedStd (std ops) := ⟨fun _ _ => rfl, fun _ => rfl⟩

/-- Only library calls use done. Each nonlibrary body keeps its supplied full
oracle program. This is a concrete source interpretation, not a blanket
no-read assertion about opaque verifier bodies. -/
def implementation (ops : Ops) (body : Implementation) : Implementation :=
  fun call => if operationId call ∈ VTop_OracleStages.libraryIds
    then .done (invoke (install ops) call) else body call

theorem library_values (ops : Ops) (trusted : TrustedStd ops)
    {A : Type} (call : Call A) (library : operationId call ∈ VTop_OracleStages.libraryIds) :
    invoke (install ops) call = invoke (install (std ops)) call := by
  cases call <;> simp only [operationId, VTop_OracleStages.libraryIds, List.mem_cons,
    List.not_mem_nil, or_false, Nat.reduceEqDiff, or_self] at library
  all_goals try contradiction
  all_goals first | exact trusted.option_ok_or _ _ | exact trusted.result_unwrap32 _ | rfl

theorem library_no_read (ops : Ops) (body : Implementation)
    {A : Type} (call : Call A) (library : operationId call ∈ VTop_OracleStages.libraryIds)
    (H : Bytes → State) :
    eval H (implementation ops body call) = ([], invoke (install ops) call) := by
  simp only [implementation, if_pos library, eval]

/-- Discharges precisely the library field of ConeJoins for these concrete
source/model interpretations. The thirteen body joins remain independent. -/
theorem library_join (ops : Ops) (trusted : TrustedStd ops)
    (sourceBody modelBody : Implementation)
    {A : Type} (call : Call A) (library : operationId call ∈ VTop_OracleStages.libraryIds)
    (H : Bytes → State) (value : A)
    (_accepted : (eval H (implementation ops sourceBody call)).2 = .ok value) :
    eval H (implementation ops sourceBody call) =
      eval H (implementation (std ops) modelBody call) := by
  rw [library_no_read _ _ _ library, library_no_read _ _ _ library,
    library_values ops trusted call library]

theorem release_mark (ops : Ops) (body : Implementation) (phase : verifier.Phase)
    (H : Bytes → State) :
    eval H (implementation ops body (.op13 none phase)) = ([], .ok ()) := rfl

#print axioms std_semantics
#print axioms library_values
#print axioms library_no_read
#print axioms library_join
#print axioms release_mark
end AspisR1.Port1_Library
end
