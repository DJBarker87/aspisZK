import SdkD_First
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_FirstOrder
open Aeneas Aeneas.Std Result AspisR1CurrentCaller SdkD_Control
attribute [local irreducible] verifier.candidate.prepare

theorem accepted (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (obs : Option (verifier.Phase → Result Unit))
    (saved : alloc.vec.Vec U8) (before after : List Site)
    (success : run (SdkD_First.code ops D semantic pub proof split hash obs) before =
      (.ok (.Ok saved),after)) :
    after = before ++ [.batch0,.query0,.save] := by
  unfold SdkD_First.code at success
  repeat' first
  | (solve | cases success)
  | (fail_if_no_progress simp only [run,Bind.bind,SdkD_Control.bind,emit,liftResult,liftM,MonadLift.monadLift,MonadLiftT.monadLift] at success)
  | uncase_result
  | head_reduce success
  | split at success
  all_goals
    have same := congrArg Prod.snd success
    simpa only [Prod.snd,List.append_assoc,List.singleton_append] using same.symm

#print axioms accepted
end AspisR1.SdkD_FirstOrder
end
