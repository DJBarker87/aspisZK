import Port15DRIVER_TX1
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port15DRIVER_Driver
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port15DRIVER_Local Port15DRIVER_Cost

def sites (w : Nat → Nat) : List Nat :=
  [w 3,0,3,0,w 17,0,0,0,0,0,0,0,0,563,0,w 11,w 10,w 6,w 9,0,0,w 19]

theorem tx2 (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (H : Bytes → State) :
    Fits (Port9OR_Installed.implementation ops reserved unwrap rest) H
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash none) (sites w) := by
  unfold sites
  repeat' first
    | control_node
    | (apply Port15DRIVER_Local.library; simp [operationId, VTop_OracleStages.libraryIds])
    | (refine Nat.le_trans (Port15DRIVER_Local.delegated ops reserved unwrap rest w budgets _ _ ?_) ?_
       · simp [operationId, delegatedIds]
       · exact Nat.le_refl _)
    | exact Port12COUNT_Installed.batch1 _ _ _ _ _ _
    | exact Port9OR_Budget.reader_count _ _ _ _ _ _ _ _ _
    | (intro)

def delegatedWeight (w : Nat → Nat) : Nat :=
  2*w 3+w 4+2*w 6+w 7+2*w 9+2*w 10+2*w 11+w 12+w 17+w 19

theorem done_tail_length {A B : Type} (H : Bytes → State)
    (p : Program Bytes State A) (f : A → B) :
    (eval H (AspisV8R19.OracleProgramOps.bind p (fun a => .done (f a)))).1.length =
      (eval H p).1.length := by
  rw [eval_bind]
  simp only [eval, List.append_nil]

theorem stages (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State) :
    (eval H (Port1_Driver.stages (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash semantic pub proof)).1.length ≤ 1046 + delegatedWeight w := by
  have joined : (eval H (Port1_Driver.stages
      (Port9OR_Installed.implementation ops reserved unwrap rest) D hash semantic pub proof)).1.length ≤
      (Port15DRIVER_TX1.sites w).sum + (sites w).sum := by
    unfold Port1_Driver.stages
    apply Port12COUNT_Installed.program_bind_bound H _ _ (Port15DRIVER_TX1.sites w).sum (sites w).sum
    · exact Port15DRIVER_TX1.tx1 ops reserved unwrap rest w budgets D hash semantic pub proof H
    · intro first
      cases first with
      | fail e => exact Nat.zero_le _
      | div => exact Nat.zero_le _
      | ok result =>
        cases result with
        | Err e => exact Nat.zero_le _
        | Ok saved =>
          rw [done_tail_length]
          exact tx2 ops reserved unwrap rest w budgets D hash pub proof saved.deref H
  simp only [Port15DRIVER_TX1.sites, sites, List.sum_cons, List.sum_nil] at joined
  unfold delegatedWeight
  omega

theorem rust (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    (adapter : AdapterRw.Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (i : OraclePortStoredExperimentC4.Input) :
    (eval H (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash i)).1.length ≤ 1046 + delegatedWeight w := by
  unfold Port1_Driver.rust
  repeat' first
    | exact stages ops reserved unwrap rest w budgets D hash _ _ _ H
    | exact Nat.zero_le _
    | (split)

theorem rust1161 (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    (weighted : delegatedWeight w ≤ 115) (adapter : AdapterRw.Ops)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (i : OraclePortStoredExperimentC4.Input) :
    (eval H (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest)
      D hash i)).1.length ≤ 1161 := by
  have bounded := rust ops reserved unwrap rest w budgets adapter D hash H i
  omega

#print axioms done_tail_length
#print axioms tx2
#print axioms stages
#print axioms rust
#print axioms rust1161
set_option pp.universes true in
#print rust1161
#print stages
#print rust
#print tx2
#print LocalBudgets
#print delegatedIds
#print delegatedWeight
#print Port15DRIVER_TX1.sites
#print sites
#print Port1_Driver.stages
#print Port1_Driver.rust
end AspisR1.Port15DRIVER_Driver
end
