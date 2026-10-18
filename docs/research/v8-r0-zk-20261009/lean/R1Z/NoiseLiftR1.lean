import R1Z.PredicateR1

/-! J13-R1 (DESIGN-ii-prime §2.0, §2.1; DESIGN-R1-PRIVACY-MODEL §3.3, §4): the
noise lift, Step N of clause (ii′).

The lane word spaces and the two lift premises are imported unchanged from
R1-3's `R1Z.PredicateR1` (`OwnCell`, `ownRead`, `obs`, `Wsem`, `Wh1`, `Vsem`,
`Ph1`, `C1Lift`, `H1Lift`; built against branch
codex/r0-r1z-relations-20261018 at d26660a69).

* Lane separability (§2.0): the own cells of lane `l` of `L τ` read only
  `τ l`, so `ownRead l (L τ) = obs l (τ l)` (`own_L_eq_obs`).
* The noise tape writes the semantic lanes through `eligibleLinear`, H1 through
  the padding only, and nothing else (`noise_lane_sem`, `noise_lane_h1`,
  `noise_lane_other`); eligible noise is assembled column by column
  (`assemble`, `eligibleLinear_assemble`).
* `noise_lift`: from `∀ c, C1Lift c` and `H1Lift`, every trace whose semantic
  lanes lie in `Wsem` and whose H1 lane lies in `Wh1` has its own cells on
  lanes 0..15 and 26 reproduced by one noise tape, which is own-silent on the
  other lanes.  Bat-generic; `noise_lift_R1` takes the two lifts from `P_R1`.

C1Lift and H1Lift are hypotheses (conjuncts of P_R1, D29); nothing here
asserts them.  No row set is enumerated. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.NoiseLiftR1

open scoped BigOperators
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12
open R0Z.K4 R1Z.Batched R1Z.PredicateR1

attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows
  dotLinear claimsLinear extraLinear batchLinear

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

/-! ### Lane separability (DESIGN-ii-prime §2.0) -/

theorem L_pointClaim_congr (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (l : Fin 29) (τ τ' : Trace K) (hτ : τ l = τ' l) (j : Fin 3) :
    R0Z.PayloadSplit.L (Bat := Bat) π B ch τ (.pointClaim j l) =
      R0Z.PayloadSplit.L (Bat := Bat) π B ch τ' (.pointClaim j l) := by
  rw [R0Z.Shift.L_pointClaim, R0Z.Shift.L_pointClaim]
  simp only [honestClaims, hτ]

theorem L_extraClaim_congr (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (l : Fin 29) (τ τ' : Trace K) (hτ : τ l = τ' l) :
    R0Z.PayloadSplit.L (Bat := Bat) π B ch τ (.extraClaim l) =
      R0Z.PayloadSplit.L (Bat := Bat) π B ch τ' (.extraClaim l) := by
  rw [R0Z.Shift.L_extraClaim, R0Z.Shift.L_extraClaim]
  unfold R0P.Mask.honestExtra
  congr 1
  funext j
  show τ l (π.symm j) = τ' l (π.symm j)
  rw [hτ]

theorem L_ood_congr (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (l : Fin 29) (τ τ' : Trace K) (hτ : τ l = τ' l) (j : Fin 2) :
    R0Z.PayloadSplit.L (Bat := Bat) π B ch τ (.ood j l) =
      R0Z.PayloadSplit.L (Bat := Bat) π B ch τ' (.ood j l) := by
  simp only [R0Z.PayloadSplit.L, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    linearPayload, hτ]

theorem L_opened_congr (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (l : Fin 29) (τ τ' : Trace K) (hτ : τ l = τ' l) (q : Fin 262144) (s : Fin 4) :
    R0Z.PayloadSplit.L (Bat := Bat) π B ch τ (.opened q s l) =
      R0Z.PayloadSplit.L (Bat := Bat) π B ch τ' (.opened q s l) := by
  simp only [R0Z.PayloadSplit.L, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    linearPayload]
  split_ifs <;> simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.zero_apply, hτ]

/-- The own cells of lane `l` of `L τ` depend only on `τ l`. -/
theorem L_own_congr (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (l : Fin 29) (τ τ' : Trace K) (hτ : τ l = τ' l) :
    ownRead (Bat := Bat) (F := F) l (R0Z.PayloadSplit.L π B ch τ) =
      ownRead (Bat := Bat) (F := F) l (R0Z.PayloadSplit.L π B ch τ') := by
  funext o
  cases o with
  | claim j => exact L_pointClaim_congr (Bat := Bat) π B ch l τ τ' hτ j
  | extra => exact L_extraClaim_congr (Bat := Bat) π B ch l τ τ' hτ
  | ood j => exact L_ood_congr (Bat := Bat) π B ch l τ τ' hτ j
  | opened q s => exact L_opened_congr (Bat := Bat) π B ch l τ τ' hτ q s

/-- DESIGN-ii-prime §2.0: `own_l (L τ) = obs_l (τ l)` for every trace. -/
theorem own_L_eq_obs (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (l : Fin 29) (τ : Trace K) :
    ownRead (Bat := Bat) (F := F) l (R0Z.PayloadSplit.L π B ch τ) = obs (Bat := Bat) π B ch l (τ l) := by
  simp only [obs, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  apply L_own_congr
  first
    | exact (Pi.single_eq_same _ _).symm
    | simp

theorem ownRead_A (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (l : Fin 29) (t : T K F) :
    ownRead (Bat := Bat) (F := F) l (A π B ch t) =
      ownRead (Bat := Bat) (F := F) l (R0Z.PayloadSplit.L π B ch (R0Z.JointTrace.tapeLinear B t)) := by
  have hA : A (Bat := Bat) π B ch t =
      R0Z.PayloadSplit.L π B ch (R0Z.JointTrace.tapeLinear B t) := rfl
  rw [hA]

/-! ### The lanes written by the noise tape -/

theorem noise_lane_sem (B : PackBasis F) (p : ExtTape F) (e : EligibleNoise K F) (l : Fin 29)
    (hl : l.val < 16) :
    R0Z.JointTrace.tapeLinear B (inrN (p, e)) l = R0Z.JointTrace.eligibleLinear e l := by
  funext r
  have h0 : traceLinear B (aff (inrN (p, e) : T K F)) l r = 0 := by
    simp only [traceLinear, LinearMap.pi_apply, if_pos hl, LinearMap.zero_apply]
  show R0Z.JointTrace.eligibleLinear e l r + traceLinear B (aff (inrN (p, e))) l r = _
  rw [h0, add_zero]

theorem noise_lane_h1 (B : PackBasis F) (p : ExtTape F) (e : EligibleNoise K F) :
    R0Z.JointTrace.tapeLinear B (inrN (p, e)) 26 =
      R0Z.JointTrace.tapeLinear B (inrN (LinearMap.inl F (ExtTape F) (EligibleNoise K F) p)) 26 := by
  funext r
  have h : ¬ ((26 : Fin 29).val < 16) := by decide
  have hz : ∀ e' : EligibleNoise K F, R0Z.JointTrace.eligibleLinear e' 26 r = 0 := by
    intro e'
    rw [R0Z.JointTrace.eligibleLinear_apply, if_neg h]
  show R0Z.JointTrace.eligibleLinear e 26 r + traceLinear B (aff (inrN (p, e))) 26 r =
    R0Z.JointTrace.eligibleLinear (0 : EligibleNoise K F) 26 r +
      traceLinear B (aff (inrN (p, (0 : EligibleNoise K F)))) 26 r
  rw [hz, hz]
  all_goals rfl

theorem noise_lane_other (B : PackBasis F) (n : N K F) (l : Fin 29)
    (hl : ¬ (l.val < 16 ∨ l.val = 26)) :
    R0Z.JointTrace.tapeLinear B (inrN n) l = 0 := by
  funext r
  have h16 : ¬ l.val < 16 := fun h => hl (Or.inl h)
  have h26 : ¬ l.val = 26 := fun h => hl (Or.inr h)
  have he : R0Z.JointTrace.eligibleLinear n.2 l r = 0 := by
    rw [R0Z.JointTrace.eligibleLinear_apply, if_neg h16]
  show R0Z.JointTrace.eligibleLinear n.2 l r + traceLinear B (aff (inrN n)) l r = 0
  rw [he, zero_add]
  by_cases h2 : l.val < 26
  · simp only [traceLinear, LinearMap.pi_apply, h16, h2, ↓reduceIte, ↓reduceDIte]
    apply balance_zero_generic
    intro s
    rfl
  · by_cases h4 : l.val = 27
    · simp only [traceLinear, LinearMap.pi_apply, h16, h2, h26, h4, ↓reduceIte, ↓reduceDIte]
      apply balance_zero_generic
      intro s
      change (0 : K) + B.i * 0 + B.u * 0 + (B.i * B.u) * 0 = 0
      ring
    · simp only [traceLinear, LinearMap.pi_apply, h16, h2, h26, h4, ↓reduceIte, ↓reduceDIte]
      apply balance_zero_generic
      intro s
      change (0 : K) + B.i * 0 + B.u * 0 + (B.i * B.u) * 0 = 0
      ring

/-! ### Column-wise assembly of eligible noise -/

theorem eligible_col_lt {c : Fin 29} {r : Fin 1024} (h : eligible c r) : c.val < 16 := And.left h

/-- Take column `c` of the noise from `E c`. -/
def assemble (E : Fin 16 → EligibleNoise K F) : EligibleNoise K F :=
  fun cell => E ⟨cell.1.1.val, eligible_col_lt cell.2⟩ cell

theorem eligibleLinear_assemble (E : Fin 16 → EligibleNoise K F) (c : Fin 16) :
    R0Z.JointTrace.eligibleLinear (assemble E) (Fin.castLE (by omega) c) =
      R0Z.JointTrace.eligibleLinear (E c) (Fin.castLE (by omega) c) := by
  funext r
  have hs : ∀ s, semanticNoise (Sum.elim (assemble E) 0) (Fin.castLE (by omega) c) s =
      semanticNoise (Sum.elim (E c) 0) (Fin.castLE (by omega) c) s := by
    intro s
    unfold semanticNoise
    split_ifs <;> rfl
  rw [R0Z.JointTrace.eligibleLinear_apply, R0Z.JointTrace.eligibleLinear_apply]
  simp only [hs]

/-! ### Step N -/

/-- DESIGN-ii-prime §2.1 `noise_lift`, Bat-generic, with the lifts as premises. -/
theorem noise_lift (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K)
    (hC : ∀ c : Fin 16, C1Lift (Bat := Bat) π B ch c) (hH : H1Lift (Bat := Bat) π B hB ch)
    (δ : Trace K) (hδ : ∀ c : Fin 16, δ (Fin.castLE (by omega) c) ∈ Wsem (K := K) (F := F))
    (hδ26 : δ 26 ∈ Wh1 B hB) :
    ∃ n : N K F,
      (∀ l : Fin 29, (l.val < 16 ∨ l.val = 26) →
        ownRead (Bat := Bat) (F := F) l (A π B ch (inrN n)) =
          ownRead (Bat := Bat) (F := F) l (R0Z.PayloadSplit.L π B ch δ)) ∧
      (∀ l : Fin 29, ¬ (l.val < 16 ∨ l.val = 26) →
        ownRead (Bat := Bat) (F := F) l (A π B ch (inrN n)) = 0) := by
  have hc : ∀ c : Fin 16, ∃ e : EligibleNoise K F,
      obs (Bat := Bat) π B ch (Fin.castLE (by omega) c)
          (R0Z.JointTrace.eligibleLinear e (Fin.castLE (by omega) c)) =
        obs (Bat := Bat) π B ch (Fin.castLE (by omega) c) (δ (Fin.castLE (by omega) c)) := by
    intro c
    obtain ⟨v, hv, hvo⟩ := hC c (Submodule.mem_map_of_mem (hδ c))
    obtain ⟨e, he⟩ := LinearMap.mem_range.1 hv
    have he' : R0Z.JointTrace.eligibleLinear e (Fin.castLE (by omega) c) = v := he
    exact ⟨e, by rw [he', hvo]⟩
  choose E hE using hc
  obtain ⟨v, hv, hvo⟩ := hH (Submodule.mem_map_of_mem hδ26)
  obtain ⟨p, hp⟩ := LinearMap.mem_range.1 hv
  have hp' : R0Z.JointTrace.tapeLinear B
      (inrN (LinearMap.inl F (ExtTape F) (EligibleNoise K F) p)) 26 = v := hp
  have key : ∀ c : Fin 16,
      ownRead (Bat := Bat) (F := F) (Fin.castLE (by omega) c) (A π B ch (inrN (p, assemble E))) =
        ownRead (Bat := Bat) (F := F) (Fin.castLE (by omega) c) (R0Z.PayloadSplit.L π B ch δ) := by
    intro c
    rw [ownRead_A, own_L_eq_obs, own_L_eq_obs, noise_lane_sem B p _ _ c.isLt,
      eligibleLinear_assemble]
    exact hE c
  refine ⟨(p, assemble E), ?_, ?_⟩
  · intro l hl
    rcases hl with h16 | h26
    · have hl' : l = Fin.castLE (by omega) (⟨l.val, h16⟩ : Fin 16) := Fin.ext rfl
      rw [hl']
      exact key _
    · obtain rfl : l = 26 := Fin.ext h26
      rw [ownRead_A, own_L_eq_obs, own_L_eq_obs, noise_lane_h1, hp', hvo]
  · intro l hl
    rw [ownRead_A, own_L_eq_obs, noise_lane_other B _ l hl, map_zero]

/-! ### Named accessors for the conjuncts of `P_R1` (LOG D36.3) -/

section Accessors
variable {π : Fin 1024 ≃ Fin 1024} {B : PackBasis F} {hB : PackField B} {ch : Challenges K}

theorem _root_.R1Z.PredicateR1.P_R1.halfOK (hP : P_R1 π B hB ch) : HalfOK ch := hP.1

theorem _root_.R1Z.PredicateR1.P_R1.semK4 (hP : P_R1 π B hB ch) : SemK4 B hB ch := hP.2.1

theorem _root_.R1Z.PredicateR1.P_R1.bcondG (hP : P_R1 π B hB ch) : BCondG_R1 π B ch := hP.2.2.2.1

theorem _root_.R1Z.PredicateR1.P_R1.c1lift (hP : P_R1 π B hB ch) :
    ∀ c : Fin 16, C1Lift (Bat := R1Bat) π B ch c := hP.2.2.2.2.1

theorem _root_.R1Z.PredicateR1.P_R1.h1lift (hP : P_R1 π B hB ch) :
    H1Lift (Bat := R1Bat) π B hB ch := hP.2.2.2.2.2.1

theorem _root_.R1Z.PredicateR1.P_R1.queryCard (hP : P_R1 π B hB ch) : QueryCard ch :=
  hP.2.2.2.2.2.2

end Accessors

/-- Step N for the R1 instance: both lifts are conjuncts of `P_R1`. -/
theorem noise_lift_R1 (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) (hP : P_R1 π B hB ch)
    (δ : Trace K) (hδ : ∀ c : Fin 16, δ (Fin.castLE (by omega) c) ∈ Wsem (K := K) (F := F))
    (hδ26 : δ 26 ∈ Wh1 B hB) :
    ∃ n : N K F,
      (∀ l : Fin 29, (l.val < 16 ∨ l.val = 26) →
        ownRead (Bat := R1Bat) (F := F) l (A π B ch (inrN n)) =
          ownRead (Bat := R1Bat) (F := F) l (R0Z.PayloadSplit.L π B ch δ)) ∧
      (∀ l : Fin 29, ¬ (l.val < 16 ∨ l.val = 26) →
        ownRead (Bat := R1Bat) (F := F) l (A π B ch (inrN n)) = 0) :=
  noise_lift (Bat := R1Bat) π B hB ch hP.c1lift hP.h1lift δ hδ hδ26

#print axioms L_pointClaim_congr
#print axioms L_extraClaim_congr
#print axioms L_ood_congr
#print axioms L_opened_congr
#print axioms L_own_congr
#print axioms own_L_eq_obs
#print axioms ownRead_A
#print axioms noise_lane_sem
#print axioms noise_lane_h1
#print axioms noise_lane_other
#print axioms assemble
#print axioms eligibleLinear_assemble
#print axioms noise_lift
#print axioms R1Z.PredicateR1.P_R1.halfOK
#print axioms R1Z.PredicateR1.P_R1.semK4
#print axioms R1Z.PredicateR1.P_R1.bcondG
#print axioms R1Z.PredicateR1.P_R1.c1lift
#print axioms R1Z.PredicateR1.P_R1.h1lift
#print axioms R1Z.PredicateR1.P_R1.queryCard
#print axioms noise_lift_R1
end R1Z.NoiseLiftR1
