import Port12COUNT_Rows
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_Levels
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConeNodeDomain MultiproofConeLevelIteration Port12COUNT_Potential Port12COUNT_Rows
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The actual level cut n=w preserves the unspent row credit. -/
theorem level {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (physical : Slice U8) (s : reference.Scratch)
    (domain : Domain physical s) :
    let out := eval H (Port9OR_Code.program D hash (Port9OR_P6Levels.level s physical))
    out.1.length + retained (levelPost physical) out.2 ≤ credit physical s 0#usize 0#usize :=
  rows D hash H physical s.n.val s 0#usize 0#usize
    ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩

/-- All heights symbolically, all read replies and partial native hash policies. -/
theorem levels {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (physical : Slice U8) (height : Nat)
    (s : reference.Scratch) (domain : Domain physical s) :
    let out := eval H (Port9OR_Code.program D hash (Port9OR_P6Levels.levels height s physical))
    out.1.length + retained (levelPost physical) out.2 ≤ credit physical s 0#usize 0#usize := by
  induction height generalizing s with
  | zero => change 0 + credit physical s 0#usize 0#usize ≤ credit physical s 0#usize 0#usize; omega
  | succ height ih =>
    simp only [Port9OR_P6Levels.levels]
    rw [eval_join]
    have first := level D hash H physical s domain
    cases ran : eval H (Port9OR_Code.program D hash (Port9OR_P6Levels.level s physical)) with
    | mk log result =>
      simp only [ran] at first
      cases result with
      | fail e => exact first
      | div => exact first
      | ok out =>
        cases out with
        | Stop stopped =>
          change (log ++ []).length + 0 ≤ _
          simpa only [retained,levelPost,List.append_nil,Nat.add_zero] using first
        | Done next =>
          have sourceRan := Port9OR_Code.value D hash (Port9OR_P6Levels.level s physical) H
          rw [ran,Port9OR_P6Levels.level_source (Port9OR_Code.native D H) hash s physical domain] at sourceRan
          have nextDomain := Port9OR_P6Levels.level_preserve (Port9OR_Code.native D H) hash s next physical domain sourceRan.symm
          have tail := ih next nextDomain
          simp only [retained,levelPost] at first
          simp only [List.length_append]
          omega

theorem count {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (physical : Slice U8) (height : Nat)
    (s : reference.Scratch) (domain : Domain physical s) :
    (eval H (Port9OR_Code.program D hash (Port9OR_P6Levels.levels height s physical))).1.length ≤
      (physical.val.length-s.at.val)/32+s.n.val-1 := by
  have bound := levels D hash H physical height s domain
  change _ + _ ≤ (physical.val.length-s.at.val)/32+s.n.val-1 at bound
  omega

#print axioms level
#print axioms levels
#print axioms count
end AspisR1.Port12COUNT_Levels
end
