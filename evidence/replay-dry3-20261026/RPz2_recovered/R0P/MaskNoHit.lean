import R0P.MaskPrefix

/-! Absence of a masked classifier hit excludes eta and alpha events for
any candidate trace selected by the opening witness. -/
set_option autoImplicit false
namespace R0P.Mask
open R0P R0P.SemSource R0P.SemD3Glue R0C.SemStatement Polynomial R0P.Sumcheck
open AspisPool.AlgorithmicCircleDecoderV7 AspisR0.ListsResponses
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Lambda LambdaRows
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem semSlotZ (rs : List (MsgZ K × ChalZ K)) (cs : List K)
    (hp : semChalsZ rs = some cs) (i : Fin rs.length) :
    ∃ sm, rs[i.val] = (.semantic sm, .semantic (cs.getD i.val 0)) := by
  obtain ⟨sm,hs⟩ := semChalsZ_getElem rs cs hp i
  refine ⟨sm, ?_⟩
  have hi : i.val < cs.length := by rw [semChalsZ_length rs cs hp]; exact i.isLt
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using hs

theorem no_hit_eta {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (fallback1 : AspisR0.ChordGeometry.Point K) (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    (B : PackBasis F) (x : TypedContext K Sfield) (rs tail : List (MsgZ K × ChalZ K))
    (hlen : rs.length = 25) (cs : List K) (hparse : semChalsZ rs = some cs)
    (claim : K) (hclaim : claimOf rs = some claim)
    (hw gw : InitialWord K) (hc2 : c2OfZ rs = some (hw,gw))
    (t : Trace K) (ht : t ∈ LambdaRows x.transport (c2Words x hw gw))
    (hno : ¬ hitFrom (sourceDataWithFallbackZ fallback1 maskClaims B) x [] (rs ++ tail)) :
    ¬ etaBad claim (maskTotal maskClaims x.transport t)
      (originalTotal x.pub B t (fun j => cs.getD j.val 0)) (cs.getD 14 0) := by
  intro hb
  have htlen : (rs.take 14).length = 14 := by simp only [List.length_take, hlen]; omega
  have hpre : (fun j : Fin 14 => (cs.take 14).getD j.val 0) = (fun j => cs.getD j.val 0) := by
    funext j; exact getD_take_lt cs 14 j.val j.isLt
  obtain ⟨sm,hslot⟩ := semSlotZ rs cs hparse ⟨14,by omega⟩
  have hm := claimOf_getElem rs claim (by omega) hclaim
  rw [hslot] at hm
  have hsm : sm = .maskSum claim := Msg.semantic.inj hm
  subst sm
  apply no_hit_roundZ fallback1 maskClaims B x rs tail hno ⟨14,by omega⟩
  rw [hslot]
  apply Or.inl
  refine ⟨.maskSum claim, cs.getD 14 0, ?_, rfl, rfl, ?_⟩
  · change (rs.take 14).length < 25; omega
  · constructor
    · intro hh
      change 15 ≤ (rs.take 14).length at hh
      omega
    · simp only [htlen, show ¬ (14 : Nat) < 14 by omega,
        semChalsZ_take rs cs hparse 14, hpre]
      exact ⟨t, candidate_memZ x rs hw gw hc2 t ht 14 (by omega) (by omega), hb⟩

#print axioms semSlotZ
#print axioms no_hit_eta

theorem no_hit_alpha {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (fallback1 : AspisR0.ChordGeometry.Point K) (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    (B : PackBasis F) (x : TypedContext K Sfield) (rs tail : List (MsgZ K × ChalZ K))
    (hlen : rs.length = 25) (cs : List K) (hparse : semChalsZ rs = some cs)
    (claim : K) (hclaim : claimOf rs = some claim)
    (polys : Fin 10 → K[X]) (hpolys : semPolysZ rs = some polys)
    (hdegree : ∀ j, (polys j).natDegree ≤ 27)
    (hw gw : InitialWord K) (hc2 : c2OfZ rs = some (hw,gw))
    (t : Trace K) (ht : t ∈ LambdaRows x.transport (c2Words x hw gw))
    (hno : ¬ hitFrom (sourceDataWithFallbackZ fallback1 maskClaims B) x [] (rs ++ tail)) :
    ¬ badAlpha 27 10
      (virtualPolyZ maskClaims x.transport x.pub B t (fun j => cs.getD j.val 0) (cs.getD 14 0))
      polys (fun j => cs.getD (15+j.val) 0) := by
  intro hb
  obtain ⟨j,hj⟩ := (badAlpha_iff_exists_round 27 10 _ polys _).mp hb
  let n := 15+j.val
  have hn : n < rs.length := by dsimp [n]; omega
  have htn : (rs.take n).length = n := List.length_take_of_le (by omega)
  obtain ⟨sm,hslot⟩ := semSlotZ rs cs hparse ⟨n,hn⟩
  have hm := semPolysZ_getElem rs polys hlen hpolys j
  change (rs[n]'hn).1 = .semantic (.base (.roundPoly (polys j))) at hm
  rw [hslot] at hm
  have hsm : sm = .base (.roundPoly (polys j)) := Msg.semantic.inj hm
  subst sm
  have hpre : (fun k : Fin 14 => (cs.take n).getD k.val 0) = (fun k => cs.getD k.val 0) := by
    funext k; exact getD_take_lt cs n k.val (by dsimp [n]; omega)
  have heta : (cs.take n).getD 14 0 = cs.getD 14 0 := getD_take_lt cs n 14 (by dsimp [n]; omega)
  have hpref : (fun k : Fin j.val => (cs.take n).getD (15+k.val) 0) =
      alphaRoundPrefix (fun k : Fin 10 => cs.getD (15+k.val) 0) j := by
    funext k
    exact getD_take_lt cs n (15+k.val) (by dsimp [n]; omega)
  apply no_hit_roundZ fallback1 maskClaims B x rs tail hno ⟨n,hn⟩
  rw [hslot]
  apply Or.inl
  refine ⟨.base (.roundPoly (polys j)), cs.getD n 0, ?_, rfl, rfl, ?_⟩
  · change (rs.take n).length < 25; dsimp [n] at *; omega
  · constructor
    · intro _; exact hdegree j
    · have hparsepre := semChalsZ_take rs cs hparse n
      have hclaimpre := (claimOf_take rs n (by dsimp [n]; omega)).trans hclaim
      simp only [htn, show ¬ n < 14 by dsimp [n]; omega,
        show n ≠ 14 by dsimp [n]; omega, show n < 25 by dsimp [n]; omega,
        hparsepre, hclaimpre, hpre, heta, ↓reduceDIte, ↓reduceIte]
      have hidx : (⟨(rs.take n).length-15,by rw [htn]; dsimp [n]; omega⟩ : Fin 10) = j := by
        apply Fin.ext
        change (rs.take n).length - 15 = j.val
        rw [htn]
        exact Nat.add_sub_cancel_left 15 j.val
      refine ⟨t, candidate_memZ x rs hw gw hc2 t ht n (by dsimp [n]; omega) (by omega), ?_⟩
      have lift (k : Fin 10) (he : k = j) :
          alphaRound 27 10
            (virtualPolyZ maskClaims x.transport x.pub B t (fun k => cs.getD k.val 0) (cs.getD 14 0))
            (fun _ => polys j) k (fun l : Fin k.val => (cs.take n).getD (15+l.val) 0)
            (cs.getD n 0) := by
        subst k
        rw [hpref]
        exact hj
      exact lift _ hidx

#print axioms no_hit_alpha

end
end R0P.Mask
