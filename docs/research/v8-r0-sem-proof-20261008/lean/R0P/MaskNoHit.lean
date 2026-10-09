import R0P.MaskPrefix

/-! Absence of a masked classifier hit excludes eta and alpha events for
any candidate trace selected by the opening witness. -/
set_option autoImplicit false
namespace R0P.Mask
open R0P R0P.SemSource R0P.SemD3Glue R0C.SemStatement Polynomial R0P.Sumcheck
open AspisPool.AlgorithmicCircleDecoderV7 AspisR0.ListsResponses
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Lambda
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
    (fallback1 : AspisR0.ChordGeometry.Point K) (maskPoly : (Fin 10 → K) → K)
    (B : PackBasis F) (x : TypedContext K Sfield) (rs tail : List (MsgZ K × ChalZ K))
    (hlen : rs.length = 25) (cs : List K) (hparse : semChalsZ rs = some cs)
    (claim : K) (hclaim : claimOf rs = some claim)
    (hw gw : InitialWord K) (hc2 : c2OfZ rs = some (hw,gw))
    (t : Trace K) (ht : t ∈ Lambda (c2Words x hw gw))
    (hno : ¬ hitFrom (sourceDataWithFallbackZ fallback1 maskPoly B) x [] (rs ++ tail)) :
    ¬ etaBad claim (maskTotal maskPoly)
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
  apply no_hit_roundZ fallback1 maskPoly B x rs tail hno ⟨14,by omega⟩
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
end
end R0P.Mask
