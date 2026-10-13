import R0P.SemD2

/-! G18 structural padding and prefix-polynomial plumbing.

The λ/χ events use copy endpoints whose pattern columns are in `Fin 16`,
so changing trace lanes 26 and 27 leaves them unchanged. Before the C2
commitment, the zero-word padding preserves every agreement position of a
candidate with the padded width-29 tuple. -/
set_option autoImplicit false
namespace R0P.SemSource

open R0P R0C.SemStatement AspisPool.AlgorithmicCircleDecoderV7
  AspisR0.ListsResponses AspisWide.InitialEncoder AspisWide.Agreement
  AspisV6Width29CorrelatedAgreement Polynomial

attribute [local irreducible] Lambda LambdaRows

noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {Sfield : Fin 29 → Subfield K}

#print axioms padC2Trace

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem padC2Trace_apply (t : Trace K) (l : Fin 29)
    (h26 : l ≠ 26) (h27 : l ≠ 27) : padC2Trace t l = t l := by
  simp only [padC2Trace, Function.update_of_ne h27,
    Function.update_of_ne h26]

#print axioms padC2Trace_apply

private theorem exactInitialEncoder_zero :
    exactInitialEncoder (0 : InitialMessage K) = (0 : InitialWord K) := by
  simpa only [exactInitialLinear_apply] using exactInitialLinear.map_zero

#print axioms exactInitialEncoder_zero

private theorem padWord_eq_zero : padWord = (0 : InitialWord K) := by
  exact exactInitialEncoder_zero

#print axioms padWord_eq_zero

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem copyEndpointTuple_pad (t : Trace K) (tag : Nat) (ep : CopyEndpoint) :
    copyEndpointTuple (padC2Trace t) tag ep = copyEndpointTuple t tag ep := by
  unfold copyEndpointTuple
  apply Prod.ext
  · rfl
  · change copyPatternTuple (copyPatterns ep.pattern)
        (fun c => padC2Trace t (Fin.castLE (by omega) c) ep.row) =
      copyPatternTuple (copyPatterns ep.pattern)
        (fun c => t (Fin.castLE (by omega) c) ep.row)
    apply congrArg (copyPatternTuple (copyPatterns ep.pattern))
    funext c
    let l : Fin 29 := Fin.castLE (by omega) c
    have h26 : l ≠ 26 := by
      intro he
      have : l.val = 26 := congrArg Fin.val he
      dsimp [l] at this
      omega
    have h27 : l ≠ 27 := by
      intro he
      have : l.val = 27 := congrArg Fin.val he
      dsimp [l] at this
      omega
    exact congrArg (fun word : InitialMessage K => word ep.row)
      (padC2Trace_apply t l h26 h27)

#print axioms copyEndpointTuple_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem copyProducerTuple_pad (t : Trace K) (link : CopyLink) :
    copyProducerTuple (padC2Trace t) link = copyProducerTuple t link := by
  exact copyEndpointTuple_pad t link.tag link.producer

#print axioms copyProducerTuple_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem copyConsumerTuple_pad (t : Trace K) (link : CopyLink) :
    copyConsumerTuple (padC2Trace t) link = copyConsumerTuple t link := by
  exact copyEndpointTuple_pad t link.tag link.consumer

#print axioms copyConsumerTuple_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem prodVal_pad (t : Trace K) (lam : K) (link : CopyLink) :
    prodVal (padC2Trace t) lam link = prodVal t lam link := by
  simp only [prodVal, copyProducerTuple_pad]

#print axioms prodVal_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem consVal_pad (t : Trace K) (lam : K) (link : CopyLink) :
    consVal (padC2Trace t) lam link = consVal t lam link := by
  simp only [consVal, copyConsumerTuple_pad]

#print axioms consVal_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem map_prodVal_pad (xs : List CopyLink) (t : Trace K) (lam : K) :
    xs.map (prodVal (padC2Trace t) lam) = xs.map (prodVal t lam) := by
  induction xs with
  | nil => rfl
  | cons link xs ih => simp only [List.map_cons, prodVal_pad, ih]

#print axioms map_prodVal_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem map_consVal_pad (xs : List CopyLink) (t : Trace K) (lam : K) :
    xs.map (consVal (padC2Trace t) lam) = xs.map (consVal t lam) := by
  induction xs with
  | nil => rfl
  | cons link xs ih => simp only [List.map_cons, consVal_pad, ih]

#print axioms map_consVal_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem prodPolys_pad (pub : Public K) (t : Trace K) :
    prodPolys pub (padC2Trace t) = prodPolys pub t := by
  simp only [prodPolys, copyProducerTuple_pad]

#print axioms prodPolys_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem consPolys_pad (pub : Public K) (t : Trace K) :
    consPolys pub (padC2Trace t) = consPolys pub t := by
  simp only [consPolys, copyConsumerTuple_pad]

#print axioms consPolys_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem poleSet_pad (t : Trace K) (lam : K) :
    poleSet (padC2Trace t) lam = poleSet t lam := by
  unfold poleSet
  rw [map_prodVal_pad, map_consVal_pad]

#print axioms poleSet_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem valueSet_pad (pub : Public K) (t : Trace K) (lam : K) :
    valueSet pub (padC2Trace t) lam = valueSet pub t lam := by
  unfold valueSet
  rw [map_prodVal_pad, map_consVal_pad]

#print axioms valueSet_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem signedCount_pad (pub : Public K) (t : Trace K) (lam v : K) :
    signedCount pub (padC2Trace t) lam v = signedCount pub t lam v := by
  classical
  have hprod : prodVal (padC2Trace t) lam = prodVal t lam :=
    funext (prodVal_pad t lam)
  have hcons : consVal (padC2Trace t) lam = consVal t lam :=
    funext (consVal_pad t lam)
  unfold signedCount
  rw [hprod, hcons]

#print axioms signedCount_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- The fixed λ-round event is invariant under zeroing the two C2 lanes. -/
theorem lambdaRoundBad_pad (pub : Public K) (t : Trace K) (lam : K) :
    lambdaRoundBad pub (padC2Trace t) lam ↔ lambdaRoundBad pub t lam := by
  simp only [lambdaRoundBad, productDifference, prodPolys_pad, consPolys_pad]

#print axioms lambdaRoundBad_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- The fixed χ-round event is invariant under zeroing the two C2 lanes. -/
theorem chiRoundBad_pad (pub : Public K) (t : Trace K) (lam chi : K) :
    chiRoundBad pub (padC2Trace t) lam chi ↔ chiRoundBad pub t lam chi := by
  unfold chiRoundBad
  have hcount : signedCount pub (padC2Trace t) lam = signedCount pub t lam := by
    funext v
    exact signedCount_pad pub t lam v
  rw [poleSet_pad, valueSet_pad, hcount]

private theorem padAgreement_lane26 (x : TypedContext K Sfield) (t : Trace K)
    (r : Fin 1048576) :
    c2Words x padWord padWord 26 r = exactInitialEncoder (padC2Trace t 26) r := by
  have hword : c2Words x padWord padWord 26 = padWord := by
    change Function.update (Function.update x.W 26 padWord) 27 padWord 26 = padWord
    rw [Function.update_of_ne (by decide), Function.update_self]
  have htrace : padC2Trace t 26 = (0 : InitialMessage K) := by
    change Function.update (Function.update t 26 0) 27 0 26 = 0
    rw [Function.update_of_ne (by decide), Function.update_self]
  rw [hword, padWord_eq_zero, htrace, exactInitialEncoder_zero]

#print axioms padAgreement_lane26

private theorem padAgreement_lane27 (x : TypedContext K Sfield) (t : Trace K)
    (r : Fin 1048576) :
    c2Words x padWord padWord 27 r = exactInitialEncoder (padC2Trace t 27) r := by
  have hword : c2Words x padWord padWord 27 = padWord := by
    change Function.update (Function.update x.W 26 padWord) 27 padWord 27 = padWord
    rw [Function.update_self]
  have htrace : padC2Trace t 27 = (0 : InitialMessage K) := by
    change Function.update (Function.update t 26 0) 27 0 27 = 0
    rw [Function.update_self]
  rw [hword, padWord_eq_zero, htrace, exactInitialEncoder_zero]

#print axioms padAgreement_lane27

#print axioms chiRoundBad_pad

/-- Padding both not-yet-committed lanes preserves every original joint
agreement position with the C2 words, so it preserves Lambda membership. -/
private theorem mem_Lambda_pad_coeffs (x : TypedContext K Sfield) (h g : InitialWord K)
    (t : Trace K) (ht : t ∈ Lambda (c2Words x h g)) :
    padC2Trace t ∈ Lambda (c2Words x padWord padWord) := by
  have hbound : 38230 ≤
      (width29JointAgreementSet exactInitialEncoder (c2Words x h g) t).card :=
    (mem_Lambda _ _).mp ht
  have hincl :
      width29JointAgreementSet exactInitialEncoder (c2Words x h g) t ⊆
        width29JointAgreementSet exactInitialEncoder (c2Words x padWord padWord)
          (padC2Trace t) := by
    intro r hr
    simp only [width29JointAgreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hr ⊢
    intro l
    by_cases h26 : l = 26
    · subst l
      exact padAgreement_lane26 x t r
    · by_cases h27 : l = 27
      · subst l
        exact padAgreement_lane27 x t r
      · have hleft : c2Words x h g l = x.W l := by
          simp only [c2Words, Function.update_of_ne h27,
            Function.update_of_ne h26]
        have hright : c2Words x padWord padWord l = x.W l := by
          simp only [c2Words, Function.update_of_ne h27,
            Function.update_of_ne h26]
        have htrace : padC2Trace t l = t l := padC2Trace_apply t l h26 h27
        have htraceEncoder : exactInitialEncoder (padC2Trace t l) =
            exactInitialEncoder (t l) := congrArg exactInitialEncoder htrace
        have hrl := hr l
        rw [hleft] at hrl
        rw [htraceEncoder, hright]
        exact hrl
  apply (mem_Lambda _ _).mpr
  exact hbound.trans (Finset.card_le_card hincl)

theorem mem_Lambda_pad (x : TypedContext K Sfield) (h g : InitialWord K)
    (t : Trace K) (ht : t ∈ LambdaRows x.transport (c2Words x h g)) :
    padC2Trace t ∈ LambdaRows x.transport (c2Words x padWord padWord) := by
  rw [mem_LambdaRows] at ht ⊢
  rw [coeffsOf_padC2Trace]
  exact mem_Lambda_pad_coeffs x h g (coeffsOf x.transport t) ht

#print axioms mem_Lambda_pad

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- In the α phase, `semRoundBad` observes an adaptive strategy only at its
current component `i - 14`, with the actual fourteen- and α-prefixes. -/
theorem semRoundBad_strat_congr {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat₁ strat₂ : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (i : Fin 24) (pref : Fin i.val → K) (x : K) (hi : 14 ≤ i.val)
    (hstrat : strat₁ (semSlice pref 0 14)
        ⟨i.val - 14, by omega⟩ (semSlice pref 14 (i.val - 14)) =
      strat₂ (semSlice pref 0 14)
        ⟨i.val - 14, by omega⟩ (semSlice pref 14 (i.val - 14))) :
    semRoundBad t pub B G strat₁ i pref x ↔ semRoundBad t pub B G strat₂ i pref x := by
  have h0 : i.val ≠ 0 := by omega
  have h1 : i.val ≠ 1 := by omega
  have h2 : i.val ≠ 2 := by omega
  have hz : ¬ i.val < 13 := by omega
  have hm : i.val ≠ 13 := by omega
  simp only [semRoundBad, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg hz,
    dif_neg hm]
  rw [hstrat]

#print axioms semRoundBad_strat_congr

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem semPolys_getElem
    (rounds : List (Msg K K (SemMsg K) × Chal K K))
    (polys : Fin 10 → K[X]) (hrounds : rounds.length = 24)
    (hparsed : semPolys rounds = some polys) (j : Fin 10) :
    (rounds[14 + j.val]'(by omega)).1 = .semantic (.roundPoly (polys j)) := by
  simp only [semPolys, dif_pos hrounds] at hparsed
  split at hparsed
  · rename_i hall
    have hfun := Option.some.inj hparsed
    have hvalue := congrFun hfun j
    have hallj := hall j
    cases hm : (rounds[14 + j.val]'(by omega)).1 with
    | semantic sm =>
      cases sm with
      | roundPoly p =>
        simp [hm] at hvalue
        have hp : p = polys j := hvalue
        rw [hp]
      | none => simp [hm] at hallj
      | h1 h g => simp [hm] at hallj
    | beforeZ0 y => simp [hm] at hallj
    | beforeZ1 y => simp [hm] at hallj
    | opening om => simp [hm] at hallj
  · simp at hparsed

#print axioms semPolys_getElem

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- At an α round of a 24-round parsed transcript, the polynomial selected
from the prefix and current message is the polynomial parsed at that slot. -/
theorem polysOf_prefix (rounds : List (Msg K K (SemMsg K) × Chal K K))
    (polys : Fin 10 → K[X]) (i : Fin 24) (hi : 14 ≤ i.val)
    (hrounds : rounds.length = 24) (hparsed : semPolys rounds = some polys)
    (sm : SemMsg K)
    (hcurrent : (rounds[i.val]'(by omega)).1 = .semantic sm) :
    polysOf (rounds.take i.val) sm ⟨i.val - 14, by omega⟩ =
      polys ⟨i.val - 14, by omega⟩ := by
  let j : Fin 10 := ⟨i.val - 14, by omega⟩
  have hidx : 14 + j.val = i.val := by dsimp [j]; omega
  have hslot := semPolys_getElem rounds polys hrounds hparsed j
  have hslot' : (rounds[i.val]'(by omega)).1 =
      .semantic (.roundPoly (polys j)) := by
    simpa only [hidx] using hslot
  have hcur : sm = .roundPoly (polys j) := by
    rw [hcurrent] at hslot'
    cases sm with
    | none => cases hslot'
    | h1 h g => cases hslot'
    | roundPoly p =>
      injection hslot' with hp
  have htake : (rounds.take i.val).length = i.val := by
    simp [hrounds]
  change polysOf (rounds.take i.val) sm j = polys j
  unfold polysOf
  rw [dif_neg (by omega), if_pos (by omega), hcur]

#print axioms polysOf_prefix

end
end R0P.SemSource
