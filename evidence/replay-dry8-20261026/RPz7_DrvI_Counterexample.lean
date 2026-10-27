import RPz7_EndP_Headline
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvI_Counterexample
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- An ordinary typed implementation, with no connection to the installed SDK. -/
def silent : VTop_OracleCode.Implementation := fun _ => .done .div

/-- Same result, but a real oracle query occurs even on the rejected prefix. -/
def queried : VTop_OracleCode.Implementation := fun _ => .ask [] (fun _ => .done .div)

theorem call_results {A : Type} (call : VTop_Trace.Call A) (H : Bytes → State) :
    (eval H (silent call)).2 = (eval H (queried call)).2 := rfl

theorem call_trace (H : Bytes → State) :
    eval H (silent VTop_Trace.Call.op16) ≠ eval H (queried VTop_Trace.Call.op16) := by
  intro equal
  have logs := congrArg (fun v => v.1.length) equal
  change 0 = 1 at logs
  exact Nat.zero_ne_one logs

theorem silent_stages {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) :
    Port1_Driver.stages silent D hash semantic pub proof = .done false := by
  rfl

theorem queried_stages {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) :
    Port1_Driver.stages queried D hash semantic pub proof =
      .ask [] (fun _ => .done false) := by
  rfl

/-- The SAME digest, semantic input and byte slices do not determine source
Programs when Implementation is arbitrary. This includes rejected prefixes. -/
theorem stages_differ {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (semantic : Port1_Driver.Semantic) (pub proof : Slice U8)
    (H : Bytes → State) :
    eval H (Port1_Driver.stages silent D hash semantic pub proof) ≠
      eval H (Port1_Driver.stages queried D hash semantic pub proof) := by
  rw [silent_stages, queried_stages]
  intro equal
  have logs := congrArg (fun v => v.1.length) equal
  change 0 = 1 at logs
  exact Nat.zero_ne_one logs

/-- No fixed deployed stage Program can be the interpretation of EVERY typed
Implementation. Does not refute existence of one compatible implementation. -/
theorem no_universal_identification {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8)
    (source : Program Bytes State Bool) (H : Bytes → State) :
    ¬ (∀ impl : VTop_OracleCode.Implementation,
      eval H (Port1_Driver.stages impl D hash semantic pub proof) = eval H source) := by
  intro all
  exact stages_differ D hash semantic pub proof H ((all silent).trans (all queried).symm)

#print axioms call_results
#print axioms call_trace
#print axioms silent_stages
#print axioms queried_stages
#print axioms stages_differ
#print axioms no_universal_identification
end AspisR1.DrvI_Counterexample
end
