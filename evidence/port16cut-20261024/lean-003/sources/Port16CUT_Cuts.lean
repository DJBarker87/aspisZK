import Port16CUT_TX2
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port16CUT_Cuts
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port15DRIVER_Local

@[irreducible] def sourceOne (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) :
    Program Bytes State (Result (core.result.Result (alloc.vec.Vec U8) verifier.Error)) :=
  interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none)

@[irreducible] def sourceTwo (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (pub proof checkpoint : Slice U8) :
    Program Bytes State (Result (core.result.Result Unit verifier.Error)) :=
  interpret impl (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash none)

theorem sourceOne_eq (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) :
    sourceOne impl D hash semantic pub proof =
      interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none) := by
  unfold sourceOne
  rfl

theorem sourceTwo_eq (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (pub proof checkpoint : Slice U8) :
    sourceTwo impl D hash pub proof checkpoint =
      interpret impl (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash none) := by
  unfold sourceTwo
  rfl

def oneWeight (w : Nat → Nat) : Nat := 480+w 3+w 4+w 7+w 12+w 11+w 10+w 6+w 9
def twoWeight (w : Nat → Nat) : Nat := 566+w 3+w 17+w 11+w 10+w 6+w 9+w 19
def delegatedWeight (w : Nat → Nat) : Nat :=
  2*w 3+w 4+2*w 6+w 7+2*w 9+2*w 10+2*w 11+w 12+w 17+w 19

theorem sourceOne_bound (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
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
      (Port15DRIVER_TX1.tx1 ops reserved unwrap rest w budgets D hash semantic pub proof H)
  simp only [Port15DRIVER_TX1.sites, List.sum_cons, List.sum_nil] at h
  unfold oneWeight
  omega

theorem sourceTwo_bound (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
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
      (Port16CUT_TX2.tx2 ops reserved unwrap rest w budgets D hash pub proof checkpoint H)
  simp only [Port16CUT_TX2.sites, List.sum_cons, List.sum_nil] at h
  unfold twoWeight
  omega

theorem weights (w : Nat → Nat) : oneWeight w + twoWeight w = 1046 + delegatedWeight w := by
  unfold oneWeight twoWeight delegatedWeight
  omega

#print axioms sourceOne
#print axioms sourceTwo
#print axioms sourceOne_eq
#print axioms sourceTwo_eq
#print axioms sourceOne_bound
#print axioms sourceTwo_bound
#print axioms weights
end AspisR1.Port16CUT_Cuts
end
