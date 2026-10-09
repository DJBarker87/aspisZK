import R0P.MaskPrefix

/-! The first fourteen events are the frozen semantic events. C2 padding
and candidate membership are preserved before the inserted eta row. -/
set_option autoImplicit false
namespace R0P.Mask
open R0P R0P.SemSource R0P.SemD3Glue R0C.SemStatement Polynomial R0P.Sumcheck
open AspisPool.AlgorithmicCircleDecoderV7 AspisR0.ListsResponses
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Lambda
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem early_candidate_to_prefixZ {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (maskPoly : (Fin 10 → K) → K) (B : PackBasis F) (x : TypedContext K Sfield)
    (rs : List (MsgZ K × ChalZ K)) (hlen : rs.length = 25)
    (cs : List K) (hparse : semChalsZ rs = some cs)
    (hw gw : InitialWord K) (hc2 : c2OfZ rs = some (hw,gw))
    (t : Trace K) (ht : t ∈ Lambda (c2Words x hw gw)) (i : Fin 24) (hi : i.val < 14)
    (sm : SemMsgZ K) (hcurrent : (rs[i.val]'(by omega)).1 = .semantic sm)
    (hbad : candidateRoundBad x.pub B t (fun _ => 0) (fun j => cs.getD j.val 0) i) :
    semanticBadZ maskPoly B ⟨x,rs.take i.val⟩ sm (cs.getD i.val 0) := by
  have htake : (rs.take i.val).length = i.val := List.length_take_of_le (by omega)
  have hblen : (baseRoundsZ rs).length = 25 := by simp only [baseRoundsZ, List.length_map, hlen]
  have hbcur : ((baseRoundsZ rs)[i.val]'(by omega)).1 = .semantic (unmaskSem sm) := by
    simp only [baseRoundsZ, List.getElem_map, hcurrent, unmaskMsg]
  have hpre : (fun j : Fin i.val => (cs.take i.val).getD j.val 0) =
      semPrefix (fun j : Fin 24 => cs.getD j.val 0) i := by
    funext j
    exact getD_take_lt cs i.val j.val j.isLt
  have hfinish (u : Trace K)
      (hu : u ∈ candidates x (baseRoundsZ (rs.take i.val)) (unmaskSem sm))
      (hb : semRoundBad u x.pub B (fun pre => virtualPoly x.pub B u pre)
        (fixedStrat (polysOf (baseRoundsZ (rs.take i.val)) (unmaskSem sm))) i
        (semPrefix (fun j : Fin 24 => cs.getD j.val 0) i) (cs.getD i.val 0)) :
      semanticBadZ maskPoly B ⟨x,rs.take i.val⟩ sm (cs.getD i.val 0) := by
    constructor
    · intro h; change 15 ≤ (rs.take i.val).length at h; omega
    · rw [dif_pos (show (rs.take i.val).length < 14 by omega)]
      have hl : (baseRoundsZ (rs.take i.val)).length = i.val := by
        simp only [baseRoundsZ, List.length_map, htake]
      refine ⟨by change (baseRoundsZ (rs.take i.val)).length < 24; omega, cs.take i.val,
        (semChalsZ_base _).trans (semChalsZ_take rs cs hparse i.val), ?_, u, hu, ?_⟩
      · intro h; change 14 ≤ (baseRoundsZ (rs.take i.val)).length at h; omega
      · have lift (k : Fin 24) (he : k = i) :
            semRoundBad u x.pub B (fun pre => virtualPoly x.pub B u pre)
              (fixedStrat (polysOf (baseRoundsZ (rs.take i.val)) (unmaskSem sm))) k
              (fun j : Fin k.val => (cs.take i.val).getD j.val 0) (cs.getD i.val 0) := by
          subst k
          rw [hpre]
          exact hb
        exact lift _ (Fin.ext hl)
  by_cases hi2 : i.val < 2
  · apply hfinish (padC2Trace t)
    · have hmem := candidate_mem_before_c2N x (baseRoundsZ rs) 25 hblen hw gw t ht
        ⟨i.val,by omega⟩ hi2 (unmaskSem sm)
      simpa only [baseRoundsZ, List.map_take] using hmem
    · exact (semRoundBad_pad_early t x.pub B _ _ i _ _ hi2).mpr hbad
  · apply hfinish t
    · have hmem := candidate_mem_after_c2N x (baseRoundsZ rs) 25 hblen hw gw hc2 t ht
        ⟨i.val,by omega⟩ (by change 2 ≤ i.val; omega) (unmaskSem sm) hbcur
      simpa only [baseRoundsZ, List.map_take] using hmem
    · exact (semRoundBad_strat_early t x.pub B _ _ _ i _ _ hi).mpr hbad

#print axioms early_candidate_to_prefixZ
end
end R0P.Mask
