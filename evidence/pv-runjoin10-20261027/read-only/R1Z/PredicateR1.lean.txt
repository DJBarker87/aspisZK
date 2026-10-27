import R1Z.VerifierRelationsR1

/-! R1-3 (DESIGN-R1-PRIVACY-MODEL §3, §4; LOG D30.3, D34): the public
rejection predicate `P_R1` of the R1 prover, as a conjunction of named Props.

* `QPrime_R1`: (Q′) on the R1 instance.
* `V_G`, `BCondG_R1 := B0R1' ≤ V_G`, and the two consequences `bcond_of_G`
  (BCond, for clause (i′)) and `breach_of_G` (BReach, for clause (ii′)), from
  `bat_ker_own_le_B0R1'`.  `B0R1' := B0R1 ⊓ (unopened folded cells zero)`:
  the unprimed `B0R1 ≤ V_G` is false for every challenge, because `relR1`
  never constrains the folded cells outside `FoldedOpen` while `V_G` is zero
  there (Z9b, LOG design correction).  The number of independent relations
  varies with the query set (queries sharing a parent u/4 give coinciding
  line relations); nothing here counts relations.
* `C1Lift`, `H1Lift` (the (ii′) noise lifts, design §3.3), stated
  Bat-generically and specialised to `R1Bat` in `P_R1`.
* `HalfOK`, `SemK4`, `QueryCard`.

Every conjunct is a function of (π, B, hB, ch) only.  Nothing here asserts
any conjunct. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.PredicateR1

open scoped BigOperators
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12 R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ## (Q′) -/

/-- (Q′) for R1 (design §3.1): `ChainT0K4 ≤ (ker own).map roundMaskMap`. -/
def QPrime_R1 (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) : Prop :=
  R0Z.SilentReduction.QPrime (Bat := R1Bat) π B hB ch

/-! ## (B) in the V_G = B0 form -/

/-- Mask tapes with only G limbs: zero mask-only raw part, zero D limbs. -/
def Gonly : Submodule F (M K F) :=
  LinearMap.ker (LinearMap.fst F (Fin 10 × Fin 1024 → F) (ExtTape F × ExtTape F)) ⊓
    LinearMap.ker ((LinearMap.snd F (ExtTape F) (ExtTape F)).comp
      (LinearMap.snd F (Fin 10 × Fin 1024 → F) (ExtTape F × ExtTape F)))

/-- Batched image of G-only, round-silent, own-silent mask tapes. -/
def V_G (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) :
    Submodule F (R1Bat → K) :=
  ((Gonly (K := K) (F := F)) ⊓
      LinearMap.ker (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch) ⊓
      LinearMap.ker (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch)).map
    (R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch)

/-- Batched vectors whose folded cells vanish outside `FoldedOpen`. -/
def unopenedZero (ch : Challenges K) : Submodule F (R1Bat → K) where
  carrier := {b | ∀ p, ¬ FoldedOpen ch p → b (.folded p) = 0}
  add_mem' := by
    intro a b ha hb p hp
    rw [Pi.add_apply, ha p hp, hb p hp, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c b hb p hp
    rw [Pi.smul_apply, hb p hp, smul_zero]

/-- `B0`, corrected: relation-consistent batched vectors with zero unopened
folded cells. -/
def B0R1' (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : Submodule F (R1Bat → K) :=
  B0R1 (F := F) π ch ⊓ unopenedZero ch

/-- Every mask tape has zero batched cells at the unopened folded positions. -/
theorem batMap_unopened (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (m : M K F) (p : Fin 262144) (hp : ¬ FoldedOpen ch p) :
    R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch m (.folded p) = 0 := by
  have e : R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch m (.folded p) =
      BatchedLayer.read (Bat := R1Bat) π ch (pureTrace B m) (.folded p) := by
    rw [R0Z.SilentReduction.batMap, LinearMap.comp_apply, R0Z.PureRounds.A_pure]
    rfl
  rw [e]
  exact folded_unqueried_zero π ch (pureTrace B m) p hp

/-- The batched image of own-silent mask tapes lies in `B0R1'`. -/
theorem bat_ker_own_le_B0R1' (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) :
    (LinearMap.ker (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch)).map
        (R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch) ≤ B0R1' π ch := by
  intro v hv
  refine Submodule.mem_inf.2 ⟨bat_ker_own_le_B0R1 (F := F) π B ch hv, ?_⟩
  obtain ⟨m, _, rfl⟩ := Submodule.mem_map.1 hv
  exact fun p hp => batMap_unopened π B ch m p hp

/-- Shape sanity: `B0R1'` lives on the opened coordinates. -/
theorem B0R1'_le_unopenedZero (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) :
    B0R1' (F := F) π ch ≤ unopenedZero ch := inf_le_right

/-- The (B) conjunct of `P_R1`: every relation-consistent batched vector with
zero unopened folded cells is reached by a G-only silent tape. -/
def BCondG_R1 (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) : Prop :=
  B0R1' π ch ≤ V_G π B ch

/-- (B) as used by clause (i′) (SilentReduction.BCond on R1). -/
def BCond_R1 (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) : Prop :=
  R0Z.SilentReduction.BCond (Bat := R1Bat) π B ch

/-- (B) as used by clause (ii′). -/
def BReach_R1 (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) : Prop :=
  B0R1' π ch ≤
    (LinearMap.ker (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch) ⊓
      LinearMap.ker (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch)).map
      (R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch)

theorem V_G_le (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) :
    V_G π B ch ≤
      (LinearMap.ker (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch) ⊓
        LinearMap.ker (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch)).map
        (R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch) := by
  apply Submodule.map_mono
  intro m hm
  rcases Submodule.mem_inf.1 hm with ⟨hGR, ho⟩
  exact Submodule.mem_inf.2 ⟨ho, (Submodule.mem_inf.1 hGR).2⟩

/-- Shape sanity: `V_G` also lives on the opened coordinates, so
`BCondG_R1` compares two subspaces of the same coordinate space (the
unprimed `B0R1 ≤ V_G` could never hold). -/
theorem V_G_le_unopenedZero (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) :
    V_G π B ch ≤ unopenedZero ch := by
  intro v hv
  obtain ⟨m, _, rfl⟩ := Submodule.mem_map.1 hv
  exact fun p hp => batMap_unopened π B ch m p hp

theorem breach_of_G (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (hG : BCondG_R1 π B ch) : BReach_R1 π B ch :=
  hG.trans (V_G_le π B ch)

theorem bcond_of_G (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (hG : BCondG_R1 π B ch) : BCond_R1 π B ch :=
  le_antisymm (Submodule.map_mono inf_le_left)
    ((bat_ker_own_le_B0R1' π B ch).trans (hG.trans (V_G_le π B ch)))

/-! ## The (ii′) noise lifts (design §3.3) -/

section Lifts

variable {Bat : Type} [BatchedLayer K Bat]

/-- The own cells of one lane. -/
inductive OwnCell
  | claim (j : Fin 3)
  | extra
  | ood (j : Fin 2)
  | opened (q : Fin 262144) (s : Fin 4)

/-- Read the own cells of lane `c` from a payload. -/
def ownRead (c : Fin 29) : Payload K Bat →ₗ[F] (OwnCell → K) :=
  LinearMap.pi fun o => match o with
  | .claim j => (LinearMap.proj (PayloadCell.pointClaim j c) : Payload K Bat →ₗ[F] K)
  | .extra => (LinearMap.proj (PayloadCell.extraClaim c) : Payload K Bat →ₗ[F] K)
  | .ood j => (LinearMap.proj (PayloadCell.ood j c) : Payload K Bat →ₗ[F] K)
  | .opened q s => (LinearMap.proj (PayloadCell.opened q s c) : Payload K Bat →ₗ[F] K)

/-- The own cells of lane `c` produced by a word placed in lane `c` alone. -/
def obs (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (c : Fin 29) :
    (Fin 1024 → K) →ₗ[F] (OwnCell → K) :=
  (ownRead (Bat := Bat) c).comp
    (((R0Z.PayloadSplit.L (Bat := Bat) π B ch).restrictScalars F).comp
      (LinearMap.single F (fun _ : Fin 29 => Fin 1024 → K) c))

end Lifts

/-- The base field inside `K`. -/
def baseF : Submodule F K := LinearMap.range (Algebra.linearMap F K)

/-- Sum of a lane word over the inactive rows. -/
def inactiveSumF : (Fin 1024 → K) →ₗ[F] K :=
  ∑ r ∈ copyInactiveRows, (LinearMap.proj r : (Fin 1024 → K) →ₗ[F] K)

/-- Base-field lane words with zero inactive sum. -/
def Wsem : Submodule F (Fin 1024 → K) :=
  (⨅ r : Fin 1024, (baseF (F := F)).comap (LinearMap.proj r : (Fin 1024 → K) →ₗ[F] K)) ⊓
    LinearMap.ker (inactiveSumF (K := K) (F := F))

/-- K₄-valued lane words with zero inactive sum. -/
def Wh1 (B : PackBasis F) (hB : PackField B) : Submodule F (Fin 1024 → K) :=
  (⨅ r : Fin 1024, (K4F B hB).comap (LinearMap.proj r : (Fin 1024 → K) →ₗ[F] K)) ⊓
    LinearMap.ker (inactiveSumF (K := K) (F := F))

/-- Lane `c` of the eligible semantic noise. -/
def Vsem (c : Fin 29) : Submodule F (Fin 1024 → K) :=
  LinearMap.range ((LinearMap.proj c : Trace K →ₗ[F] (Fin 1024 → K)).comp
    (R0Z.JointTrace.eligibleLinear (K := K) (F := F)))

/-- Lane 26 (H1) of the H1-padding tape. -/
def Ph1 (B : PackBasis F) : Submodule F (Fin 1024 → K) :=
  LinearMap.range ((LinearMap.proj 26 : Trace K →ₗ[F] (Fin 1024 → K)).comp
    ((R0Z.JointTrace.tapeLinear B).comp
      (inrN.comp (LinearMap.inl F (ExtTape F) (EligibleNoise K F)))))

/-- C1 lane lift (design §3.3): every own observation of a base, inactive-
balanced word in C1 lane `c` is produced by eligible noise. -/
def C1Lift {Bat : Type} [BatchedLayer K Bat] (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (c : Fin 16) : Prop :=
  (Wsem (K := K) (F := F)).map (obs (Bat := Bat) π B ch (Fin.castLE (by omega) c)) ≤
    (Vsem (Fin.castLE (by omega) c)).map (obs (Bat := Bat) π B ch (Fin.castLE (by omega) c))

/-- H1 lane lift (design §3.3). -/
def H1Lift {Bat : Type} [BatchedLayer K Bat] (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (hB : PackField B) (ch : Challenges K) : Prop :=
  (Wh1 B hB).map (obs (Bat := Bat) π B ch 26) ≤ (Ph1 B).map (obs (Bat := Bat) π B ch 26)

/-! ## Field and sampler conjuncts -/

/-- α₉ ≠ ½ (J2 / `Phi0_sRem`). -/
def HalfOK (ch : Challenges K) : Prop := alpha ch 9 ≠ 1 / 2

/-- Every semantic challenge lies in K₄. -/
def SemK4 (B : PackBasis F) (hB : PackField B) (ch : Challenges K) : Prop :=
  ∀ i : Fin 25, ch.sem i ∈ K4 B hB

/-- At most 22 queries. -/
def QueryCard (ch : Challenges K) : Prop := ch.queries.card ≤ 22

/-! ## The predicate -/

/-- The R1 honest-prover rejection predicate (design §3.4, LOG D30.3). -/
def P_R1 (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) : Prop :=
  HalfOK ch ∧ SemK4 B hB ch ∧ QPrime_R1 π B hB ch ∧ BCondG_R1 π B ch ∧
    (∀ c : Fin 16, C1Lift (Bat := R1Bat) π B ch c) ∧ H1Lift (Bat := R1Bat) π B hB ch ∧
    QueryCard ch

theorem P_R1.qprime {π : Fin 1024 ≃ Fin 1024} {B : PackBasis F} {hB : PackField B}
    {ch : Challenges K} (h : P_R1 π B hB ch) : QPrime_R1 π B hB ch := h.2.2.1

theorem P_R1.bcond {π : Fin 1024 ≃ Fin 1024} {B : PackBasis F} {hB : PackField B}
    {ch : Challenges K} (h : P_R1 π B hB ch) : BCond_R1 π B ch :=
  bcond_of_G π B ch h.2.2.2.1

theorem P_R1.breach {π : Fin 1024 ≃ Fin 1024} {B : PackBasis F} {hB : PackField B}
    {ch : Challenges K} (h : P_R1 π B hB ch) : BReach_R1 π B ch :=
  breach_of_G π B ch h.2.2.2.1

/-- Clause (i′) on Chain0₄ (design §3.6 b, first half): under `P_R1`, every
`Chain0K4` vector is the payload of a silent mask tape.  J2-R1 supplies
`sRem ∈ Chain0K4`. -/
theorem chain0K4_le_silent_R1 {π : Fin 1024 ≃ Fin 1024} {B : PackBasis F}
    {hB : PackField B} {ch : Challenges K} (h : P_R1 π B hB ch) :
    R0Z.SilentReduction.Chain0K4 (Bat := R1Bat) B hB ch ≤
      (R0Z.Z4Maps.silentMasks (Bat := R1Bat) π B ch).map
        ((A (Bat := R1Bat) π B ch).comp inlM) :=
  R0Z.SilentReduction.chain0K4_le_silent_of π B hB ch h.qprime h.bcond

#print axioms batMap_unopened
#print axioms bat_ker_own_le_B0R1'
#print axioms B0R1'_le_unopenedZero
#print axioms V_G_le_unopenedZero
#print axioms V_G_le
#print axioms breach_of_G
#print axioms bcond_of_G
#print axioms P_R1.qprime
#print axioms P_R1.bcond
#print axioms P_R1.breach
#print axioms chain0K4_le_silent_R1

end R1Z.PredicateR1

end
