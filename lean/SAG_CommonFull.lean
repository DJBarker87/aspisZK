import Tx2I_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_CommonFull
open Aeneas Aeneas.Std Result VTop_Stages
attribute [local irreducible] Tx2I_Cuts.tail

theorem reached (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit))
    (accepted : verifier.candidate.tx2_common ops D pub proof checkpoint hash obs = ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (saved : verifier.Accumulator)
      (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (returned : verifier.Accumulator) (after : verifier.BatchedWeights)
      (inactive : aspis_core.field.wide_exact.WideExact) (split round0 folded round1 : Usize),
      ops.op18 D checkpoint proof pub .S2 hash = ok (.Ok (p,saved)) ∧
      ops.op16 = ok split ∧ saved.next = split ∧
      ops.op17 29#usize p.gamma = ok g ∧
      ops.op11 p.queries saved.next 22#usize = ok (.Ok geometry) ∧
      ops.op10 saved.weights.deref = ok (.Ok pending) ∧
      ops.op6 proof p saved g obs geometry pending 22#usize = ok (.Ok (returned,after)) ∧
      ops.op22 = ok round0 ∧ ops.op15 = ok folded ∧ ops.op14 = ok round1 ∧
      Tx2I_Cuts.tail ops proof p obs inactive round0 folded round1 (returned,after) = ok (.Ok ()) := by
  rw [←Tx2I_Cuts.common_source] at accepted
  unfold Tx2I_Cuts.common at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    refine ⟨_,_,_,_,_,_,_,_,_,_,_,_,by assumption,by assumption,?_,by assumption,
      by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,accepted⟩
    simp_all only [beq_iff_eq,bne_iff_ne,ne_eq,not_not]

#print axioms reached
end AspisR1.SAG_CommonFull
end
