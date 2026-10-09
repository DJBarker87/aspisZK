import R0P.MaskNoHit

/-! The first fourteen events are the frozen semantic events. C2 padding
and candidate membership are preserved before the inserted eta row. -/
set_option autoImplicit false
namespace R0P.Mask
open R0P R0P.SemSource R0P.SemD3Glue R0C.SemStatement Polynomial R0P.Sumcheck
open R0P.SemRounds
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

theorem no_hit_early {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (fallback1 : AspisR0.ChordGeometry.Point K) (maskPoly : (Fin 10 → K) → K)
    (B : PackBasis F) (x : TypedContext K Sfield) (rs tail : List (MsgZ K × ChalZ K))
    (hlen : rs.length = 25) (cs : List K) (hparse : semChalsZ rs = some cs)
    (hw gw : InitialWord K) (hc2 : c2OfZ rs = some (hw,gw))
    (t : Trace K) (ht : t ∈ Lambda (c2Words x hw gw))
    (hno : ¬ hitFrom (sourceDataWithFallbackZ fallback1 maskPoly B) x [] (rs ++ tail)) :
    ∀ i : Fin 24, i.val < 14 →
      ¬ candidateRoundBad x.pub B t (fun _ => 0) (fun j => cs.getD j.val 0) i := by
  intro i hi hb
  obtain ⟨sm,hslot⟩ := semSlotZ rs cs hparse ⟨i.val,by omega⟩
  have hbad := early_candidate_to_prefixZ maskPoly B x rs hlen cs hparse hw gw hc2 t ht i hi sm
    (congrArg Prod.fst hslot) hb
  apply no_hit_roundZ fallback1 maskPoly B x rs tail hno ⟨i.val,by omega⟩
  rw [hslot]
  apply Or.inl
  refine ⟨sm,cs.getD i.val 0,?_,rfl,rfl,hbad⟩
  change (rs.take i.val).length < 25
  simp only [List.length_take, hlen]
  omega

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem semPrefixVal_actual (r : Fin 24 → K) (i : Fin 24)
    (k : Nat) (hk : k < i.val) :
    semPrefixVal (semPrefix r i) k = r ⟨k, hk.trans i.isLt⟩ := by
  simp only [semPrefixVal, dif_pos hk, semPrefix]
  rfl

#print axioms semPrefixVal_actual

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem semSlice_actual (r : Fin 24 → K) (start len : Nat)
    (hbound : start + len ≤ 24) (j : Fin len) :
    semSlice r start len j = r ⟨start + j.val, by omega⟩ := by
  have hj : start + j.val < 24 := by omega
  simp only [semSlice, semPrefixVal, dif_pos hj]

#print axioms semSlice_actual

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem semSlice_prefix_actual (r : Fin 24 → K) (i : Fin 24)
    (start len : Nat) (hbound : start + len ≤ i.val) :
    semSlice (semPrefix r i) start len = semSlice r start len := by
  funext j
  have hj : start + j.val < i.val := by omega
  have hj24 : start + j.val < 24 := hj.trans i.isLt
  simp only [semSlice, semPrefixVal, dif_pos hj, dif_pos hj24, semPrefix]
  rfl

#print axioms semSlice_prefix_actual

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem semRoundBad_zero {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (x : K) :
    semRoundBad t pub B G strat 0 (semPrefix r 0) x ↔ lambdaRoundBad pub t x := by
  simp [semRoundBad]

#print axioms semRoundBad_zero

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem semRoundBad_one {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (x : K) :
    semRoundBad t pub B G strat 1 (semPrefix r 1) x ↔ chiRoundBad pub t (r 0) x := by
  simp [semRoundBad, semPrefixVal, semPrefix]

#print axioms semRoundBad_one

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem semRoundBad_two {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (x : K) :
    semRoundBad t pub B G strat 2 (semPrefix r 2) x ↔
      BadTheta (laneOf t pub (r 0) (r 1) B) x := by
  simp [semRoundBad, semPrefixVal, semPrefix]

#print axioms semRoundBad_two

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem semRoundBad_zc {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (j : Fin 10) (x : K) :
    semRoundBad t pub B G strat ⟨3 + j.val, by omega⟩
        (semPrefix r ⟨3 + j.val, by omega⟩) x ↔
      zcRound 10 (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B))
        j (zcPrefix (semSlice r 3 10) j) x := by
  let i : Fin 24 := ⟨3 + j.val, by omega⟩
  change semRoundBad t pub B G strat i (semPrefix r i) x ↔ _
  have h0 : i.val ≠ 0 := by dsimp [i]; omega
  have h1 : i.val ≠ 1 := by dsimp [i]; omega
  have h2 : i.val ≠ 2 := by dsimp [i]; omega
  have hz : i.val < 13 := by dsimp [i]; omega
  have hj : (⟨i.val - 3, by dsimp [i]; omega⟩ : Fin 10) = j := by
    apply Fin.ext
    dsimp [i]
    omega
  have hp0 : semPrefixVal (semPrefix r i) 0 = r 0 :=
    semPrefixVal_actual r i 0 (by dsimp [i]; omega)
  have hp1 : semPrefixVal (semPrefix r i) 1 = r 1 :=
    semPrefixVal_actual r i 1 (by dsimp [i]; omega)
  have hp2 : semPrefixVal (semPrefix r i) 2 = r 2 :=
    semPrefixVal_actual r i 2 (by dsimp [i]; omega)
  have hslice : semSlice (semPrefix r i) 3 j.val = zcPrefix (semSlice r 3 10) j := by
    rw [semSlice_prefix_actual r i 3 j.val (by dsimp [i]; omega)]
    rfl
  simp only [semRoundBad, dif_neg h0, dif_neg h1, dif_neg h2, dif_pos hz,
    hp0, hp1, hp2]
  have hview := congrArg (fun k : Fin 10 =>
    zcRound 10 (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B))
      k (semSlice (semPrefix r i) 3 k.val) x) hj
  rw [hslice] at hview
  exact Iff.of_eq hview

#print axioms semRoundBad_zc

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem semRoundBad_mu {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (x : K) :
    semRoundBad t pub B G strat 13 (semPrefix r 13) x ↔
      BadMu
        (mle 10 (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B)) (semSlice r 3 10))
        (bsumB 10 (fun b => t 26 (rowOf b)))
        (bsumB 10 (fun b =>
          (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b))) x := by
  have h0 : (13 : Fin 24).val ≠ 0 := by omega
  have h1 : (13 : Fin 24).val ≠ 1 := by omega
  have h2 : (13 : Fin 24).val ≠ 2 := by omega
  have hz : ¬ (13 : Fin 24).val < 13 := by omega
  have hm : (13 : Fin 24).val = 13 := rfl
  have hp0 : semPrefixVal (semPrefix r 13) 0 = r 0 :=
    semPrefixVal_actual r 13 0 (by omega)
  have hp1 : semPrefixVal (semPrefix r 13) 1 = r 1 :=
    semPrefixVal_actual r 13 1 (by omega)
  have hp2 : semPrefixVal (semPrefix r 13) 2 = r 2 :=
    semPrefixVal_actual r 13 2 (by omega)
  have hslice := semSlice_prefix_actual r 13 3 10 (by omega)
  simp only [semRoundBad, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg hz,
    dif_pos hm, hp0, hp1, hp2, hslice]

#print axioms semRoundBad_mu

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem earlyRounds_cover {F : Subfield K} (t : Trace K) (pub : Public K) (B : PackBasis F)
    (r : Fin 24 → K)
    (hrounds : ∀ i, i.val < 14 → ¬ candidateRoundBad pub B t (fun _ => 0) r i) :
    (¬ BadLogUp pub t (r 0) (r 1)) ∧
    (¬ BadTheta (laneOf t pub (r 0) (r 1) B) (r 2)) ∧
    (¬ BadZc (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B)) (semSlice r 3 10)) ∧
    (¬ BadMu
      (mle 10 (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B)) (semSlice r 3 10))
      (bsumB 10 (fun b => t 26 (rowOf b)))
      (bsumB 10 (fun b =>
        (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b))) (r 13)) := by
  let G := fun pre => virtualPoly pub B t pre
  let strat := fixedStrat (fun _ : Fin 10 => (0 : K[X]))
  refine ⟨?_,?_,?_,?_⟩
  · intro hb
    rcases (badLogUp_rounds_iff pub t (r 0) (r 1)).mp hb with hchi | hlam
    · exact hrounds 1 (by omega) ((semRoundBad_one t pub B G strat r (r 1)).mpr hchi)
    · exact hrounds 0 (by omega) ((semRoundBad_zero t pub B G strat r (r 0)).mpr hlam)
  · intro hb
    exact hrounds 2 (by omega) ((semRoundBad_two t pub B G strat r (r 2)).mpr hb)
  · rintro ⟨⟨b,hb⟩,hz⟩
    have hn : lanesComp (r 2) (laneOf t pub (r 0) (r 1) B) ≠ 0 := by
      intro he; exact hb (congrFun he b)
    obtain ⟨j,hj⟩ := (zc_rounds_iff 10
      (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B)) (semSlice r 3 10)).mp ⟨hn,hz⟩
    rw [semSlice_actual r 3 10 (by omega) j] at hj
    exact hrounds ⟨3+j.val,by omega⟩ (by change 3+j.val < 14; omega) ((semRoundBad_zc t pub B G strat r j _).mpr hj)
  · intro hb
    exact hrounds 13 (by omega) ((semRoundBad_mu t pub B G strat r (r 13)).mpr hb)

#print axioms no_hit_early
#print axioms earlyRounds_cover

end
end R0P.Mask
