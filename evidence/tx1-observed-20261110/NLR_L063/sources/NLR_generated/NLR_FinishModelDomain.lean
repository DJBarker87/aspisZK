import NLR_ObservedFinish
import RPz7_S1SemanticCodeFinishExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_FinishModelDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
/-- The native child packet's source result determines SAME finish arguments
for179's semantic_finish clause. The allocator/claims specialization and all
other179 clauses remain separate; this is NOT that full domain. -/
theorem reached (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
 {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
 (sem : r1_semantic.Verified H)
 (success : (run (S1SemanticCode.verify (S1SemanticCode.finish R B) D pub bytes hash none)).2=ok (.Ok sem)) :
 ∃ (p : r1_wire.Prefix) (initial after : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges),
 PrefixAdapter.parseAccepted bytes=ok (.Ok p) ∧
 (run (S1SemanticCode.publicTranscript D pub hash p.c1_root)).2=ok (.Ok initial) ∧
 (run (S1SemanticCode.begin D p initial)).2=ok (.Ok c,after) ∧
 FinishModel.finish R B D pub p after c none=ok (.Ok sem) := by
 obtain ⟨p,initial,after,c,parseCall,publicCall,beginCall,finishCall⟩ :=
  NLR_ObservedFinish.reached (S1SemanticCode.finish R B) D pub bytes hash sem success
 refine ⟨p,initial,after,c,parseCall,publicCall,beginCall,?_⟩
 rw [←S1SemanticCode.finish_erasure,←PreparedHashCode.run_value]
 exact finishCall
#print axioms reached
set_option pp.proofs false
#print reached
end AspisR1.NLR_FinishModelDomain
end
