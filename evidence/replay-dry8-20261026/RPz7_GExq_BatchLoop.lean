import RPz7_GExq_BatchCredit
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_BatchLoop
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_CountLaws
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem loop (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (fuel : Nat) (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values) (d pos : Usize) :
    count (287+fuel) (Port9OR_BatchLoop.code base D hash proof root tree lo n slot keys fuel idx val d pos) := by
  induction fuel generalizing idx val d pos with
  | zero => exact lift_count _ _
  | succ fuel ih =>
    intro H
    have paid := GExq_BatchCredit.body base D proof root tree hash lo n slot keys idx val d pos H
    unfold Port9OR_BatchLoop.code
    change (eval H (SdkC_Oracle.program (CheckpointBytes5Effect.bind
      (Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos)
      (fun out => match out with
        | .done result => .done result
        | .cont (ni,nv,nd,np) => Port9OR_BatchLoop.code base D hash proof root tree lo n slot keys fuel ni nv nd np)))).1.length ≤ _
    rw [GExp_IdealValue.bind_program,eval_bind]
    generalize actual : eval H (SdkC_Oracle.program
      (Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos)) = run at paid ⊢
    obtain ⟨log,result⟩ := run
    cases result with
    | fail e => simpa only [eval,List.append_nil] using (show log.length ≤ 287+(fuel+1) by simp only [Nat.add_zero] at paid; omega)
    | div => simpa only [eval,List.append_nil] using (show log.length ≤ 287+(fuel+1) by simp only [Nat.add_zero] at paid; omega)
    | ok out => cases out with
      | done result =>
        simp only [SdkC_Oracle.program,eval,List.append_nil]
        simp only [GExq_BatchCredit.remaining,Nat.add_zero] at paid
        omega
      | cont next =>
        obtain ⟨ni,nv,nd,np⟩ := next
        have rest := ih ni nv nd np H
        simp only [List.length_append]
        simp only [GExq_BatchCredit.remaining] at paid
        omega

#print axioms loop
end AspisR1.GExq_BatchLoop
end
