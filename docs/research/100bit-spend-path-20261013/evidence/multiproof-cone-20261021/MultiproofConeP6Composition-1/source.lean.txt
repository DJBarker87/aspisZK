import MultiproofConeFrozen2Stage
import MultiproofConeNodeAdoption

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeP6Composition
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
open OraclePortFrozenOrder OraclePortSelectedDraft OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Node := reference.Scratch → Slice U8 → Usize → Usize → Run reference.Row

/-- Local P6 source/library boundary, NOT a whole-function certificate.
It includes the physical/window rebase, the node transition, all scratch
coordinates and the one parent callback's ordered effects. The hash reply
is supplied by the current oracle, not a constant reused across nodes. -/
def NodeGate (H : Address → Digest) (source : Node) : Prop :=
  ∀ physical, physical.val.length ≤ 5504 → ∀ s i w,
    RowDomain physical s i w → i.val < s.n.val →
    eval H (source s physical i w) = eval H (node s physical i w)

/-- Structural denotation of the shipped binary node loop at the P6
control/lowering boundary. The n=w update occurs only after the input loop. -/
def rows (source : Node) : Nat → reference.Scratch → Slice U8 → Usize → Usize → Run reference.Level
  | 0,s,_,i,w => .done (if i≥s.n then .ok (.Done {s with n:=w}) else .div)
  | fuel+1,s,physical,i,w =>
    if i≥s.n then .done (.ok (.Done {s with n:=w})) else
    MultiproofConePhysicalLevels.bindRun (source s physical i w) fun out => match out with
      | .Stop stopped => .done (.ok (.Stop stopped))
      | .Next after ni nw => rows source fuel after physical ni nw

def level (source : Node) (s : reference.Scratch) (physical : Slice U8) : Run reference.Level :=
  rows source s.n.val s physical 0#usize 0#usize

def levels (source : Node) : Nat → reference.Scratch → Slice U8 → Run reference.Level
  | 0,s,_ => .done (.ok (.Done s))
  | h+1,s,physical => MultiproofConePhysicalLevels.bindRun (level source s physical) fun out => match out with
      | .Stop stopped => .done (.ok (.Stop stopped))
      | .Done after => levels source h after physical

/-- Full ordered observations and full Result/scratch, including rejection.
The domain of every next node is derived from the extracted transition. -/
theorem rows_eq {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Address → Digest) (law : ∀ input, D.digest hash input=ok (H input))
    (source : Node) (gate : NodeGate H source)
    (physical : Slice U8) (size : physical.val.length≤5504)
    (fuel : Nat) (s : reference.Scratch) (i w : Usize) (domain : RowDomain physical s i w) :
    eval H (rows source fuel s physical i w)=
      eval H (MultiproofConePhysicalLevels.rows fuel s physical i w) := by
  induction fuel generalizing s i w with
  | zero => rfl
  | succ fuel ih =>
    by_cases halt : i≥s.n
    · simp only [rows,MultiproofConePhysicalLevels.rows,if_pos halt]
    · have active : i.val<s.n.val := by change ¬i.val≥s.n.val at halt;omega
      obtain ⟨out,result,progress⟩ := binary_step_progress D hash
        (fun input => ⟨H input,law input⟩) physical s i w domain active
      have returned : (eval H (node s physical i w)).2=ok out :=
        (node_result D hash H law s physical i w).trans result
      simp only [rows,MultiproofConePhysicalLevels.rows,if_neg halt,
        MultiproofConePhysicalLevels.bindRun,eval_bind,gate physical size s i w domain active,returned,checked]
      cases out with
      | Stop stopped => rfl
      | Next after ni nw => rw [ih after ni nw progress.2.1]

theorem level_eq {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Address → Digest) (law : ∀ input, D.digest hash input=ok (H input))
    (source : Node) (gate : NodeGate H source)
    (physical : Slice U8) (size : physical.val.length≤5504)
    (s : reference.Scratch) (domain : Domain physical s) :
    eval H (level source s physical)=eval H (MultiproofConePhysicalLevels.level s physical) := by
  exact rows_eq D hash H law source gate physical size s.n.val s _ _
    ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩

/-- Arbitrary-height source composition; only local node P6 remains.
No level identity, invariant preservation or successful-run premise remains. -/
theorem levels_eq {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Address → Digest) (law : ∀ input, D.digest hash input=ok (H input))
    (source : Node) (gate : NodeGate H source)
    (physical : Slice U8) (size : physical.val.length≤5504)
    (h : Nat) (s : reference.Scratch) (domain : Domain physical s) :
    eval H (levels source h s physical)=eval H (MultiproofConePhysicalLevels.levels h s physical) := by
  induction h generalizing s with
  | zero => rfl
  | succ h ih =>
    have returned := MultiproofConePhysicalLevels.level_result D hash H law s physical domain
    simp only [levels,MultiproofConePhysicalLevels.levels,MultiproofConePhysicalLevels.bindRun,
      eval_bind,level_eq D hash H law source gate physical size s domain]
    cases result : reference.level_rows D hash s physical 0#usize 0#usize with
    | fail e => simp only [returned,result,checked]
    | div => simp only [returned,result,checked]
    | ok out =>
      simp only [returned,result,checked]
      cases out with
      | Stop stopped => rfl
      | Done after =>
        rw [ih after (level_preserve D hash (fun input => ⟨H input,law input⟩) physical s after domain result)]

/-- The whole height-18 Result is a consequence of the node gates and kernel
iteration, not a new whole-function solver obligation. -/
theorem eighteen_owned {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Address → Digest) (law : ∀ input, D.digest hash input=ok (H input))
    (source : Node) (gate : NodeGate H source)
    (physical : Slice U8) (size : physical.val.length≤5504)
    (s : reference.Scratch) (domain : Domain physical s) :
    (eval H (levels source 18 s physical)).2=reference.levels D hash s physical 18#u32 := by
  rw [levels_eq D hash H law source gate physical size 18 s domain]
  exact MultiproofConePhysicalLevels.eighteen_result D hash H law s physical domain

#print axioms rows_eq
#print axioms level_eq
#print axioms levels_eq
#print axioms eighteen_owned
end AspisR1.MultiproofConeP6Composition
end
