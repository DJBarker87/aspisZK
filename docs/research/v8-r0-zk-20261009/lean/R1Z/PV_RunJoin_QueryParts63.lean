import R1Z.PV_RunJoin_ActualPublication60
import R1Z.PV_RJN_Bytes
/-! Exact six-field query slicing. This proves the plan keeps every byte of a
successful 832-byte query cell, without evaluating the cell or claiming success. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryParts63
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PublishSkeleton54

def split (payload : Bytes) : ProverCommitPublish43.QueryParts :=
  ⟨payload.take 480,(payload.drop 480).take 128,(payload.drop 608).take 32,
    (payload.drop 640).take 32,(payload.drop 672).take 128,(payload.drop 800).take 32⟩

theorem cut {T : Type} (xs : List T) (n m : Nat) :
    xs.take n ++ (xs.drop n).take m=xs.take (n+m) := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons x xs => simpa only [List.take_succ_cons,List.drop_succ_cons,
        List.cons_append,Nat.succ_add] using congrArg (List.cons x) (ih xs)

theorem rebuild (payload : Bytes) (size : payload.length=832) :
    ProverCommitPublish43.queryBytes (split payload)=payload := by
  simp only [split,ProverCommitPublish43.queryBytes,←List.append_assoc]
  rw [cut,cut,cut,cut,cut]
  apply List.take_of_length_le
  omega

variable [ExternalTypes] [ExternalFuns]

theorem actual (phase : PV_RunJoin_NativeControl55.Phase) (publication : prover.Publication)
    (context : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) publication)
    (i : Fin 22) (out : alloc.vec.Vec U8)
    (success : PV_RunJoin_ActualPlanSources59.queryBytes publication
      (UScalar.ofNatCore i.val (by
        have hs := ProverCommitPairCounter47.usize_large
        rw [UScalar.size_def] at hs
        have := i.isLt
        omega))=ok out)
    (size : out.length=832) :
    ProverCommitPublish43.queryBytes (PV_RunJoin_ActualPlanSources59.queryPart phase i)=bytes out.val := by
  have hp := PV_RunJoin_ActualPublication60.projection phase publication context _ out success
  change ProverCommitPublish43.queryBytes (split
    (PV_RunJoin_ActualPlanSources59.publicationBytes phase _))=bytes out.val
  rw [hp]
  apply rebuild
  rw [PV_RJN_Bytes.length]
  exact size

#print axioms split
#print axioms cut
#print axioms rebuild
#print axioms actual
end R1Z.PV_RunJoin_QueryParts63
