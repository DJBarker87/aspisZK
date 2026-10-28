import R1Z.PV_RunJoin_CompilerRejections28
import R1Z.PV_RunJoin_ControlDomain28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RejectionProof28
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_ResultDomain28 PV_RunJoin_ControlDomain28

theorem eq_wp {α : Type} (m : Result α) (a : α) :
    m = ok a ↔ wp m (fun x => x = a) := by
  constructor
  · exact fun h => ⟨a,h,rfl⟩
  · rintro ⟨x,h,rfl⟩; exact h
#print axioms eq_wp

theorem ok_ne_err {α ε : Type} (a : α) (e : ε) :
    (core.result.Result.Ok a : core.result.Result α ε) = .Err e ↔ False := by
  constructor
  · intro h; cases h
  · exact False.elim
#print axioms ok_ne_err

theorem residual_eq_wp {α ε : Type}
    (r : core.result.Result core.convert.Infallible ε) (e : ε) :
    wp (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      α (core.convert.FromSame ε) r) (fun x => x = .Err e) ↔
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      α (core.convert.FromSame ε) r = ok (.Err e) := (eq_wp _ _).symm
#print axioms residual_eq_wp

/-- Both directions include all earlier guards: a later error is only
observable if its complete successful prefix is witnessed by Path. -/
theorem error_iff [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (e : pair_trace.PoolV1PairTraceErrorV1) :
    pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Err e) ↔
      PV_RunJoin_CompilerRejections28.Path input out recipient change publicInput anchor snapshot e := by
  rw [eq_wp]
  unfold pair_forest_trace.compile_forest_from_copies PV_RunJoin_CompilerRejections28.Path
  simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq,Prod.exists]
  repeat' first
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro prefix)
    | (split <;> simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,
        Result.ok.injEq,Prod.exists])
    | rfl
#print axioms error_iff
end R1Z.PV_RunJoin_RejectionProof28
