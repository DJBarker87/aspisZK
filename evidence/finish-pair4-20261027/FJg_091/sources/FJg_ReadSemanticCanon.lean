import FJg_ReaderScalarCanon
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_ReadSemanticCanon
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem source (bytes : Slice U8) (start stop : Usize) (alpha : Array K 10#usize)
    (run : CheckpointBytes4Ops.readSemanticAlpha bytes start=ok (.Ok (alpha,stop))) :
    FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) := by
  unfold CheckpointBytes4Ops.readSemanticAlpha CheckpointBytes4Ops.semanticUsing
    CheckpointBytes4Ops.withK at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  cases Result.ok.inj run
  intro x hx
  change x∈[_,_,_,_,_,_,_,_,_,_] at hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals exact FJg_ReaderScalarCanon.k _ _ _ (by assumption)

/-- Actual native semantic helper, same returned array, without caller canon. -/
theorem native (reserved : Bool) (bytes : Slice U8) (start stop : Usize) (alpha : Array K 10#usize)
    (run : (T2Nat_ReaderOps.ops reserved).readSemanticAlpha bytes start=ok (.Ok (alpha,stop))) :
    FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) := by
  exact source bytes start stop alpha ((T2Nat_ReaderOps.semantic reserved bytes start (.Ok (alpha,stop))).mp run)
#print axioms source
#print axioms native
end AspisR1.FJg_ReadSemanticCanon
end
