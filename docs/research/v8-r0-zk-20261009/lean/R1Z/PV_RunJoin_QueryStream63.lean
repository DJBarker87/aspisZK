import R1Z.PV_RunJoin_QueryParts63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryStream63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54

def stream (f : Nat → Bytes) : Nat → Nat → Bytes
  | _,0 => []
  | start,n+1 => f start ++ stream f (start+1) n

theorem indexed (f : Nat → Bytes) (start n : Nat) :
    stream f start n=(List.ofFn (fun i : Fin n => f (start+i.val))).flatten := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [stream,ih,List.ofFn_succ,List.flatten_cons,Fin.val_zero,Fin.val_succ,Nat.add_zero]
    congr 1
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    congr 1
    omega

variable [ExternalTypes] [ExternalFuns]
def part (phase : PV_RunJoin_NativeControl55.Phase) (i : Nat) : Bytes :=
  if h : i<22 then ProverCommitPublish43.queryBytes (PV_RunJoin_ActualPlanSources59.queryPart phase ⟨i,h⟩)
  else []

theorem plan (phase : PV_RunJoin_NativeControl55.Phase) (out : Bytes) :
    ProverCommitPublish43.queries (PV_RunJoin_ActualRun.plans phase).queries out=
      out++stream (part phase) 0 22 := by
  rw [ProverCommitPublish43.query_exact,indexed]
  change out++((List.ofFn (PV_RunJoin_ActualPlanSources59.queryPart phase)).map
    ProverCommitPublish43.queryBytes).flatten=out++_
  rw [List.map_ofFn]
  congr 2

#print axioms stream
#print axioms indexed
#print axioms part
#print axioms plan
end R1Z.PV_RunJoin_QueryStream63
