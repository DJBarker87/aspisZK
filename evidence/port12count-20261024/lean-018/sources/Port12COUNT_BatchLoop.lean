import Port12COUNT_BatchTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_BatchLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values Next Out)
open Port12COUNT_Verify Port12COUNT_BatchLeaf Port12COUNT_BatchTail
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem count (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (fuel : Nat) (idx : Indices) (val : Values) (d pos cap : Usize)
    (capRead : Array.index_usize capacities slot=ok cap) (small : cap.val≤172)
    (nonzero : 0<cap.val) (nSmall : n.val<256) :
    (eval H (Port9OR_Code.program D hash
      (Port9OR_BatchLoop.code base D hash proof root tree lo n slot keys fuel idx val d pos))).1.length≤
        cap.val+d.val+2*(n.val-pos.val)-1 := by
  induction fuel generalizing idx val d pos with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    simp only [Port9OR_BatchLoop.code]
    rw [Port12COUNT_Rows.eval_join]
    have first : (eval H (Port9OR_Code.program D hash
        (Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos))).1.length≤
        if pos<n then 1 else cap.val+d.val-1 := by
      split
      · exact active base D hash H proof root tree lo n slot keys idx val d pos (by assumption)
      · exact terminal base D hash H proof root tree lo n slot keys idx val d pos cap (by assumption) capRead small
    cases ran : eval H (Port9OR_Code.program D hash
        (Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos)) with
    | mk log result =>
      simp only [ran] at first
      have budget : log.length≤cap.val+d.val+2*(n.val-pos.val)-1 := by
        split at first
        · rename_i running
          change pos.val<n.val at running
          omega
        · omega
      cases result with
      | fail e => exact budget
      | div => exact budget
      | ok out =>
        cases out with
        | done final => simpa only [Port9OR_Code.program,eval,List.append_nil] using budget
        | cont next =>
          obtain ⟨nextIdx,nextVal,nextD,nextPos⟩ := next
          have sourceRan := Port9OR_Code.value D hash
            (Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos) H
          rw [ran,Port9OR_BatchLoop.body_dictionary base D (Port9OR_Code.native D H),Port9OR_BatchStep.source] at sourceRan
          have progress := Port9OR_BatchProgress.advance base (Port9OR_Code.native D H) hash proof root tree lo n slot keys
            idx val d pos nextIdx nextVal nextD nextPos sourceRan.symm
          have shape := cont_shape base (Port9OR_Code.native D H) hash proof root tree lo n slot keys
            idx val d pos nextIdx nextVal nextD nextPos sourceRan.symm
          have nextPosValue : nextPos.val=pos.val+1 := by
            rw [progress.2,Port3_Wrapping.increment pos (by change pos.val<n.val at progress;omega)]
          have nextDBound : nextD.val≤d.val+1 := by
            rcases shape with same | inc
            · rw [same];omega
            · rw [inc,Usize.wrapping_add_val_eq]
              exact Nat.mod_le _ _
          have tail := ih nextIdx nextVal nextD nextPos
          rw [if_pos progress.1] at first
          have running : pos.val<n.val := progress.1
          simp only [List.length_append]
          omega

#print axioms count
end AspisR1.Port12COUNT_BatchLoop
end
