import R1Z.PV_RunJoin_ActualPublication60
import R1Z.PV_RJQ_QueryRange
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualQueries60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
variable [ExternalTypes] [ExternalFuns]

theorem range (phase : Phase) (p : prover.Publication)
    (context : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p) :
    PV_RunJoin_PublishSkeleton57.QueryRange p.queries := by
  obtain ⟨prepared,salts,hp,hs,hf⟩ := context
  exact PV_RJQ_QueryRange.actual PV_RunJoin_ActualRun.runs phase prepared salts p hp hs hf

theorem membership (phase : Phase) (p : prover.Publication)
    (context : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p)
    (j : Fin 262144) :
    j ∈ (PV_RunJoin_ActualRun.data phase).ch.queries ↔
      ∃ q ∈ p.queries.val, q.val=j.val := by
  have returned := PV_RunJoin_ActualPublication60.returned phase p context
  simp only [PV_RunJoin_ActualRun.data,PV_RunJoin_ActualData59.data,
    PV_RunJoin_ActualData59.challenges,PV_RunJoin_ActualData59.querySet,returned,
    List.mem_toFinset,List.mem_filterMap]
  constructor
  · rintro ⟨q,hq,hj⟩
    by_cases qr : q.val<262144
    · simp only [dif_pos qr] at hj
      exact ⟨q,hq,congrArg Fin.val (Option.some.inj hj)⟩
    · simp only [dif_neg qr] at hj
      cases hj
  · rintro ⟨q,hq,hj⟩
    have qr := range phase p context q hq
    refine ⟨q,hq,?_⟩
    rw [dif_pos qr]
    congr 1
    apply Fin.ext
    exact hj

#print axioms range
#print axioms membership
end R1Z.PV_RunJoin_ActualQueries60
