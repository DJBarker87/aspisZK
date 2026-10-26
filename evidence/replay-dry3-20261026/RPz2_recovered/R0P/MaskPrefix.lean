import R0P.MaskSource
import R0P.MaskSemantics

/-! Symbolic prefix lemmas for the inserted eta row. -/
set_option autoImplicit false
namespace R0P.Mask
open R0P R0P.SemSource R0P.SemD3Glue R0C.SemStatement Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisR0.ListsResponses
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Lambda LambdaRows
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem candidate_mem_after_c2N {Sfield : Fin 29 → Subfield K}
    (x : TypedContext K Sfield) (rs : List (Msg K K (SemMsg K) × Chal K K))
    (n : Nat) (hlen : rs.length = n) (hw gw : InitialWord K) (hc2 : c2Of rs = some (hw,gw))
    (t : Trace K) (ht : t ∈ LambdaRows x.transport (c2Words x hw gw))
    (i : Fin n) (hi : 2 ≤ i.val) (sm : SemMsg K)
    (hcurrent : (rs[i.val]'(by omega)).1 = .semantic sm) :
    t ∈ candidates x (rs.take i.val) sm := by
  have htake : (rs.take i.val).length = i.val := by simp only [List.length_take, hlen]; omega
  by_cases hi2 : i.val = 2
  · have hm := c2Of_getElem rs hw gw (by omega) hc2
    have hcurrent' : (rs[2]'(by omega)).1 = .semantic sm := by simpa only [hi2] using hcurrent
    rw [hcurrent'] at hm
    have hsm : sm = .h1 hw gw := Msg.semantic.inj hm
    unfold candidates
    rw [htake, if_neg (by omega), if_pos hi2, hsm]
    exact ht
  · have hc2' : c2Of (rs.take i.val) = some (hw,gw) := (c2Of_take rs i.val (by omega)).trans hc2
    simp only [candidates, htake, show ¬ i.val < 2 by omega, if_false, hi2, hc2']
    exact ht

#print axioms candidate_mem_after_c2N

/-- Padding supplies the pre-C2 candidate without fixing C2 before lambda. -/
theorem candidate_mem_before_c2N {Sfield : Fin 29 → Subfield K}
    (x : TypedContext K Sfield) (rs : List (Msg K K (SemMsg K) × Chal K K))
    (n : Nat) (hlen : rs.length = n) (hw gw : InitialWord K)
    (t : Trace K) (ht : t ∈ LambdaRows x.transport (c2Words x hw gw))
    (i : Fin n) (hi : i.val < 2) (sm : SemMsg K) :
    padC2Trace t ∈ candidates x (rs.take i.val) sm := by
  have htake : (rs.take i.val).length = i.val := by simp only [List.length_take, hlen]; omega
  have hne : (26 : Fin 29) ≠ 27 := by
    intro h
    have hv := congrArg Fin.val h
    change 26 = 27 at hv
    omega
  have h26 : padC2Trace t 26 = 0 := by
    simp only [padC2Trace, Function.update_of_ne hne, Function.update_self]
  have h27 : padC2Trace t 27 = 0 := by simp only [padC2Trace, Function.update_self]
  simp only [candidates, htake, if_pos hi, Finset.mem_filter]
  exact ⟨mem_Lambda_pad x hw gw t ht, h26, h27⟩

#print axioms candidate_mem_before_c2N


omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem getD_take_lt (cs : List K) (n k : Nat) (hk : k < n) :
    (cs.take n).getD k 0 = cs.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem semPolysZ_getElem (rs : List (MsgZ K × ChalZ K)) (polys : Fin 10 → K[X])
    (hlen : rs.length = 25) (hp : semPolysZ rs = some polys) (j : Fin 10) :
    (rs[15 + j.val]'(by omega)).1 = .semantic (.base (.roundPoly (polys j))) := by
  simp only [semPolysZ, dif_pos hlen] at hp
  split at hp
  · rename_i hall
    have hv := congrFun (Option.some.inj hp) j
    have hj := hall j
    cases hm : (rs[15 + j.val]'(by omega)).1 with
    | semantic sm =>
      cases sm with
      | base m =>
        cases m with
        | roundPoly p =>
          simp [hm] at hv
          rw [hv]
        | none => simp [hm] at hj
        | h1 h g => simp [hm] at hj
      | maskSum c => simp [hm] at hj
    | beforeZ0 y => simp [hm] at hj
    | beforeZ1 y => simp [hm] at hj
    | opening om => simp [hm] at hj
  · simp at hp

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem claimOf_getElem (rs : List (MsgZ K × ChalZ K)) (claim : K)
    (hlen : 14 < rs.length) (hp : claimOf rs = some claim) :
    (rs[14]'hlen).1 = .semantic (.maskSum claim) := by
  rcases he : rs[14]'hlen with ⟨m,c⟩
  simp only [claimOf, List.getElem?_eq_getElem hlen, he] at hp
  cases m with
  | semantic sm =>
    cases sm with
    | base m => cases hp
    | maskSum a =>
      have ha := Option.some.inj hp
      subst a
      rfl
  | beforeZ0 y => cases hp
  | beforeZ1 y => cases hp
  | opening om => cases hp

theorem no_hit_roundZ {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (fallback1 : AspisR0.ChordGeometry.Point K) (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    (B : PackBasis F) (x : TypedContext K Sfield) (rs tail : List (MsgZ K × ChalZ K))
    (hno : ¬ hitFrom (sourceDataWithFallbackZ fallback1 maskClaims B) x [] (rs ++ tail))
    (i : Fin rs.length) :
    ¬ roundBad (sourceDataWithFallbackZ fallback1 maskClaims B) ⟨x,rs.take i.val⟩
      (rs[i.val]).1 (rs[i.val]).2 := by
  intro hb
  apply hno
  apply roundBadZ_hitFrom _ x (rs ++ tail) [] i.val (by simp only [List.length_append]; omega)
  rw [List.nil_append, List.take_append_of_le_length (by omega), List.getElem_append_left i.isLt]
  exact hb

theorem candidate_memZ {Sfield : Fin 29 → Subfield K} (x : TypedContext K Sfield)
    (rs : List (MsgZ K × ChalZ K)) (hw gw : InitialWord K)
    (hc2 : c2OfZ rs = some (hw,gw)) (t : Trace K) (ht : t ∈ LambdaRows x.transport (c2Words x hw gw))
    (n : Nat) (hn : 2 < n) (hnlen : n ≤ rs.length) :
    t ∈ candidates x (baseRoundsZ (rs.take n)) .none := by
  have hc : c2Of (baseRoundsZ (rs.take n)) = some (hw,gw) :=
    (c2OfZ_take rs n hn).trans hc2
  have hl : (baseRoundsZ (rs.take n)).length = n := by
    simp only [baseRoundsZ, List.length_map, List.length_take, Nat.min_eq_left hnlen]
  simp only [candidates, hl, if_neg (show ¬ n < 2 by omega), if_neg (show n ≠ 2 by omega), hc]
  exact ht

#print axioms getD_take_lt
#print axioms semPolysZ_getElem
#print axioms claimOf_getElem
#print axioms no_hit_roundZ
#print axioms candidate_memZ

end
end R0P.Mask
