import PAln_OpeningStages
import F3K_SourceQueryDecode
import F3L_RhoCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_OpeningShape
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation AspisR1CurrentCaller.BorrowedClaimPrepared

theorem fields {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (out : verifier.Prepared) (scratch : Array aspis_core.field.WideExact 29#usize)
    (variant : v.variant=.S2)
    (reached : PreparedScratchReachability.Reachable closedHashBoundaries D sem v hash out scratch) :
    out.variant=.S2 ∧ out.semantic_alpha=sem.alpha ∧ out.z=sem.z ∧
    (∀ j : Fin 22,(out.queries.val[j.val]'(by simpa [out.queries.property] using j.isLt)).val<262144) ∧
    Port3_FlushInstall.Canonical (Tx1Q_Carriers.k (currentQ out.rho)) := by
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,a0,a1,rho,queries,claim,
    seed,first,serialized,second,third,unwrapped,extended1,extended2,fourth,query,last,powers,claimed,output⟩ :=
    PAln_OpeningStages.double_of_reached _ D sem v hash out scratch variant reached
  have query' : QueriesModel.queries
      (Query31ConcreteMaterializedSchedule.concreteBoundaries
        Query31ConcreteDriverTraceFacts.sourceDefaultState AspisS1M31Embedding.Total.embed)
      D t4 31#u8 v.final_message=ok (.Ok queries,t5) := query
  obtain ⟨q,_,coordinates⟩ := F3K_SourceQueryDecode.source _ _ _ _ _ _ query'
  rw [output]
  refine ⟨variant,rfl,rfl,?_,?_⟩
  · intro j
    change (queries.val[j.val]'_).val<262144
    exact lt_of_eq_of_lt (coordinates j) (q j).isLt
  · exact F3L_RhoCanonical.scalar _ _ _ _ _ _ last

#print axioms fields
end AspisR1.SAP_OpeningShape
end
