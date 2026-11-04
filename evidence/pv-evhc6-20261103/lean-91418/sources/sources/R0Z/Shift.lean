import R0Z.D12
import R0Z.GoodDensity
import R0Z.LawTransport

/-! D17.1: the payload bijection Ψ_ch of D14 (a) and D15's `Good` restriction.
D17.2 items 1–7: round evaluation by Lagrange interpolation from `VDeg`, Φ₀
vanishing on the silent image, the shifted decomposition, and perfect HVZK on
`Good` from `MaskImageOn Good`. Nothing here asserts `MaskImageOn Good`.
`dir`, `sRem` and `cTilde` are built with the round inclusion (the F-restricted
`D12.roundInclusion` and `PayloadSplit.roundInclusion` are the same function). -/
set_option autoImplicit false
noncomputable section
namespace R0Z.Shift
open R0P R0P.SemSource R0P.SemDegree R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12
  Polynomial
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

/-- D15's good challenge: `GoodAlpha` at the alpha row. -/
def Good (ch : Challenges K) : Prop := GoodAlpha (alpha ch)

/-! ### Linear reads of a payload -/

def proj (coord : PayloadCell Bat) : Payload K Bat →ₗ[K] K := LinearMap.proj coord

@[simp] theorem proj_apply (coord : PayloadCell Bat) (v : Payload K Bat) : proj coord v = v coord := rfl

/-- The round-9 polynomial read from a payload's 28 coefficient cells. -/
def round9Poly : Payload K Bat →ₗ[K] K[X] :=
  ∑ i : Fin 28, (monomial i.val).comp (proj (.semanticCoeff 9 i))

theorem round9Poly_apply (v : Payload K Bat) :
    round9Poly v = ∑ i : Fin 28, monomial i.val (v (.semanticCoeff 9 i)) := by
  simp only [round9Poly, LinearMap.sum_apply, LinearMap.comp_apply, proj_apply]

def evalRound9 (ch : Challenges K) : Payload K Bat →ₗ[K] K :=
  (Polynomial.leval (alpha ch 9)).comp round9Poly

theorem evalRound9_apply (ch : Challenges K) (v : Payload K Bat) :
    evalRound9 ch v = (round9Poly v).eval (alpha ch 9) := rfl

/-- The selected mask read from a payload's first point claims and extra claim. -/
def claimMask (B : PackBasis F) (a : Fin 10 → K) : Payload K Bat →ₗ[K] K :=
  (∑ c : Fin 16, (MaskedProtocol.maskFactors B a).c1 c •
    proj (.pointClaim 0 (Fin.castLE (by omega) c))) +
    (MaskedProtocol.maskFactors B a).explicitG • proj (.pointClaim 0 27) +
    (∑ c : Fin 10, (MaskedProtocol.maskFactors B a).maskOnly c •
      proj (.pointClaim 0 ⟨16+c.val, by omega⟩)) +
    proj (.extraClaim 28)

theorem claimMask_apply (B : PackBasis F) (a : Fin 10 → K) (v : Payload K Bat) :
    claimMask B a v = R0P.Mask.maskClaimsR0 B (fun c => v (.pointClaim 0 c))
      (fun c => v (.extraClaim c)) a := by
  simp only [claimMask, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, proj_apply, R0P.Mask.maskClaimsR0, R0P.Mask.maskValue]

/-- Z4c's Φ₀: the round-9 value at alpha 9 minus the mask read from the claims. -/
def Phi0 (B : PackBasis F) (ch : Challenges K) : Payload K Bat →ₗ[K] K :=
  evalRound9 ch - claimMask B (alpha ch)

/-! ### The direction X − ½ in round 9 -/

/-- D14's direction d(X) = X − ½ in round 9, zero elsewhere. -/
def dir : Payload K Bat :=
  PayloadSplit.roundInclusion (fun j i => if j = 9 then (X - C (1/2 : K)).coeff i.val else 0)

theorem roundInclusion_semanticCoeff (p : PayloadSplit.RoundPayload K) (j : Fin 10) (i : Fin 28) :
    PayloadSplit.roundInclusion (Bat := Bat) p (.semanticCoeff j i) = p j i := rfl

theorem roundInclusion_pointClaim (p : PayloadSplit.RoundPayload K) (j : Fin 3) (c : Fin 29) :
    PayloadSplit.roundInclusion (Bat := Bat) p (.pointClaim j c) = 0 := rfl

theorem roundInclusion_extraClaim (p : PayloadSplit.RoundPayload K) (c : Fin 29) :
    PayloadSplit.roundInclusion (Bat := Bat) p (.extraClaim c) = 0 := rfl

theorem dir_pointClaim (j : Fin 3) (c : Fin 29) : dir (K := K) (Bat := Bat) (.pointClaim j c) = 0 := rfl

theorem dir_extraClaim (c : Fin 29) : dir (K := K) (Bat := Bat) (.extraClaim c) = 0 := rfl

/-- A polynomial of degree below 28 is the sum of its first 28 monomials. -/
theorem sum_monomial_coeff (p : K[X]) (hp : p.natDegree < 28) :
    ∑ i : Fin 28, monomial i.val (p.coeff i.val) = p := by
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (p.coeff i)) 28]
  exact (as_sum_range' p 28 hp).symm

theorem claimMask_roundInclusion (B : PackBasis F) (a : Fin 10 → K)
    (p : PayloadSplit.RoundPayload K) : claimMask B a (PayloadSplit.roundInclusion (Bat := Bat) p) = 0 := by
  simp only [claimMask, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    proj_apply, roundInclusion_pointClaim, roundInclusion_extraClaim, smul_zero,
    Finset.sum_const_zero, add_zero]

theorem claimMask_dir (B : PackBasis F) (a : Fin 10 → K) : claimMask B a (dir (Bat := Bat)) = 0 :=
  claimMask_roundInclusion B a _

theorem round9Poly_roundInclusion (p : PayloadSplit.RoundPayload K) :
    round9Poly (PayloadSplit.roundInclusion (Bat := Bat) p) = ∑ i : Fin 28, monomial i.val (p 9 i) := by
  rw [round9Poly_apply]
  rfl

theorem evalRound9_roundInclusion (ch : Challenges K) (p : PayloadSplit.RoundPayload K) :
    evalRound9 ch (PayloadSplit.roundInclusion (Bat := Bat) p) =
      (∑ i : Fin 28, monomial i.val (p 9 i)).eval (alpha ch 9) := by
  rw [evalRound9_apply, round9Poly_roundInclusion]

theorem Phi0_roundInclusion (B : PackBasis F) (ch : Challenges K)
    (p : PayloadSplit.RoundPayload K) :
    Phi0 B ch (PayloadSplit.roundInclusion (Bat := Bat) p) = evalRound9 ch (PayloadSplit.roundInclusion (Bat := Bat) p) := by
  simp only [Phi0, LinearMap.sub_apply, claimMask_roundInclusion, sub_zero]

theorem round9Poly_dir : round9Poly (dir (K := K) (Bat := Bat)) = X - C (1/2 : K) := by
  unfold dir
  rw [round9Poly_roundInclusion]
  simp only [eq_self_iff_true, if_true]
  exact sum_monomial_coeff _ (by rw [natDegree_X_sub_C]; norm_num)

theorem evalRound9_dir (ch : Challenges K) : evalRound9 ch (dir (Bat := Bat)) = alpha ch 9 - 1/2 := by
  rw [evalRound9_apply, round9Poly_dir, eval_sub, eval_X, eval_C]

theorem Phi0_dir (B : PackBasis F) (ch : Challenges K) : Phi0 B ch (dir (Bat := Bat)) = alpha ch 9 - 1/2 := by
  simp only [Phi0, LinearMap.sub_apply, evalRound9_dir, claimMask_dir, sub_zero]

theorem nonRound_dir : nonRound (F := F) (dir (K := K) (Bat := Bat)) = 0 := by
  funext coord
  cases coord <;> rfl

/-! ### The original terminal read from a payload, and Ψ_ch -/

/-- η·O read from a payload's three point claims (`terminalValue` reads lanes
0–15 and 26 only). -/
def originalOf (pub : Public K) (B : PackBasis F) (ch : Challenges K) (v : Payload K Bat) : K :=
  ch.sem 14 * terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
    (fun j c => v (.pointClaim j c)) (alpha ch)

def shift (pub : Public K) (B : PackBasis F) (ch : Challenges K) (v : Payload K Bat) : Payload K Bat :=
  v + (originalOf pub B ch v * (alpha ch 9 - 1/2)⁻¹) • dir

def unshift (pub : Public K) (B : PackBasis F) (ch : Challenges K) (v : Payload K Bat) : Payload K Bat :=
  v - (originalOf pub B ch v * (alpha ch 9 - 1/2)⁻¹) • dir

theorem originalOf_add_smul_dir (pub : Public K) (B : PackBasis F) (ch : Challenges K)
    (v : Payload K Bat) (k : K) : originalOf pub B ch (v + k • dir) = originalOf pub B ch v := by
  unfold originalOf
  have h : (fun j c => (v + k • (dir : Payload K Bat)) (.pointClaim j c)) =
      fun j c => v (.pointClaim j c) := by
    funext j c
    simp only [Pi.add_apply, Pi.smul_apply, dir_pointClaim, smul_zero, add_zero]
  rw [h]

theorem originalOf_sub_smul_dir (pub : Public K) (B : PackBasis F) (ch : Challenges K)
    (v : Payload K Bat) (k : K) : originalOf pub B ch (v - k • dir) = originalOf pub B ch v := by
  rw [sub_eq_add_neg, ← neg_smul, originalOf_add_smul_dir]

theorem unshift_shift (pub : Public K) (B : PackBasis F) (ch : Challenges K) (v : Payload K Bat) :
    unshift pub B ch (shift pub B ch v) = v := by
  unfold unshift shift
  rw [originalOf_add_smul_dir]
  exact add_sub_cancel_right _ _

theorem shift_unshift (pub : Public K) (B : PackBasis F) (ch : Challenges K) (v : Payload K Bat) :
    shift pub B ch (unshift pub B ch v) = v := by
  unfold shift unshift
  rw [originalOf_sub_smul_dir]
  exact sub_add_cancel _ _

/-- Ψ_ch, defined for every challenge through the field inverse. -/
def shiftEquiv (pub : Public K) (B : PackBasis F) (ch : Challenges K) : Payload K Bat ≃ Payload K Bat where
  toFun := shift pub B ch
  invFun := unshift pub B ch
  left_inv := unshift_shift pub B ch
  right_inv := shift_unshift pub B ch

/-! ### D14's remainder s(w,n) and c̃(w); the privacy obligation on `P` -/

def sRem (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (n : N K F) : Payload K Bat :=
  roundInclusion (F := F) (g h B x w ch n) -
    (Phi0 B ch (roundInclusion (F := F) (Bat := Bat) (g h B x w ch n)) * (alpha ch 9 - 1/2)⁻¹) • dir

def cTilde (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) : Payload K Bat :=
  c h B x w ch - (originalOf x.1 B ch (c (Bat := Bat) h B x w ch) * (alpha ch 9 - 1/2)⁻¹) • dir

/-- D14 (a) restricted to the challenges satisfying `P`. `MaskImageOn Good h B x`
is the privacy obligation; it is not asserted anywhere in this module. -/
def MaskImageOn (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) : Prop :=
  (∀ ch, P ch → ∀ w n, h.public w = x.1 →
    sRem (Bat := Bat) h B x w ch n ∈ LinearMap.range ((A h.transport B ch).comp inlM)) ∧
  (∀ ch, P ch → ∀ w w', h.public w = x.1 → h.public w' = x.1 →
    cTilde (Bat := Bat) h B x w ch - cTilde h B x w' ch ∈ LinearMap.range (A h.transport B ch))

/-! ### Item 1: round evaluation from `VDeg` by Lagrange interpolation -/

/-- The 28 interpolation nodes are distinct: `K` is a `ZMod P`-algebra with
`P = 2^31 − 1`, so its characteristic exceeds 27. -/
theorem nodes_injOn :
    Set.InjOn (fun k : Fin 28 => (k.val : K)) (↑(Finset.univ : Finset (Fin 28)) : Set (Fin 28)) := by
  haveI : CharP K AspisCircleGroupOrder.P :=
    charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective _
  intro a _ b _ hab
  have hP : (28 : ℕ) ≤ AspisCircleGroupOrder.P := by norm_num [AspisCircleGroupOrder.P]
  exact Fin.ext (CharP.natCast_injOn_Iio K AspisCircleGroupOrder.P
    (lt_of_lt_of_le a.isLt hP) (lt_of_lt_of_le b.isLt hP) hab)

theorem rounds_natDegree_lt (ch : Challenges K) (j : Fin 10) (f : PayloadSplit.PointFunction K) :
    (PayloadSplit.rounds ch j f).natDegree < 28 := by
  rw [PayloadSplit.rounds_apply]
  by_cases h0 : Lagrange.interpolate Finset.univ (fun k : Fin 28 => (k.val : K))
      (fun k => ∑ tail : Fin (9-j.val) → Bool, f (roundPoint ch j (k.val : K) tail)) = 0
  · rw [h0, natDegree_zero]
    norm_num
  · rw [natDegree_lt_iff_degree_lt h0]
    have hd := Lagrange.degree_interpolate_lt
      (fun k : Fin 28 => ∑ tail : Fin (9-j.val) → Bool, f (roundPoint ch j (k.val : K) tail))
      (nodes_injOn (K := K))
    simpa only [Finset.card_univ, Fintype.card_fin] using hd

/-- The coordinate-`i` slice of a `VDeg` function is a univariate polynomial. -/
theorem vdeg_update {n : ℕ} {d : Fin n → ℕ} {G : (Fin n → K) → K} (hG : VDeg n d G)
    (i : Fin n) (v : Fin n → K) :
    ∃ p : K[X], p.natDegree ≤ d i ∧ ∀ x, p.eval x = G (Function.update v i x) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      obtain ⟨p, hp, he⟩ := hG.2 (Fin.tail v)
      refine ⟨p, hp, fun x => ?_⟩
      have hu : Function.update v 0 x = Fin.cons x (Fin.tail v) := by
        rw [← Fin.cons_self_tail v, Fin.update_cons_zero, Fin.tail_cons]
      rw [he x, hu]
    | succ i =>
      obtain ⟨p, hp, he⟩ := ih (hG.1 (v 0)) i (Fin.tail v)
      refine ⟨p, hp, fun x => ?_⟩
      rw [he x, Fin.cons_update, Fin.cons_self_tail]

theorem roundPoint_update (ch : Challenges K) (j : Fin 10) (z : K)
    (tail : Fin (9-j.val) → Bool) :
    roundPoint ch j z tail = Function.update (roundPoint ch j 0 tail) j z := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self]
    simp only [roundPoint, lt_self_iff_false, eq_self_iff_true, ↓reduceDIte]
  · rw [Function.update_of_ne hij]
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    unfold roundPoint
    split_ifs <;> first | rfl | exact absurd ‹i.val = j.val› hne

/-- Round 9 has an empty Boolean tail: its point is alpha with coordinate 9 replaced. -/
theorem roundPoint_nine (ch : Challenges K) (z : K) (tail : Fin (9 - (9 : Fin 10).val) → Bool) :
    roundPoint ch 9 z tail = Function.update (alpha ch) 9 z := by
  funext i
  by_cases hi : i = 9
  · subst hi
    rw [Function.update_self]
    simp only [roundPoint, lt_self_iff_false, eq_self_iff_true, ↓reduceDIte]
  · rw [Function.update_of_ne hi]
    have hne : i.val ≠ 9 := fun h => hi (Fin.ext h)
    have hlt : i.val < (9 : Fin 10).val := by
      show i.val < 9
      have := i.isLt
      omega
    unfold roundPoint
    rw [dif_pos hlt]

/-- D17.2 item 1. -/
theorem rounds_eval_of_vdeg (ch : Challenges K) (j : Fin 10) (f : PayloadSplit.PointFunction K)
    (hf : VDeg 10 (fun _ => 27) f) (z : K) :
    (PayloadSplit.rounds ch j f).eval z = ∑ tail : Fin (9-j.val) → Bool, f (roundPoint ch j z tail) := by
  have hex : ∀ tail : Fin (9-j.val) → Bool, ∃ p : K[X], p.natDegree ≤ 27 ∧
      ∀ x, p.eval x = f (roundPoint ch j x tail) := by
    intro tail
    obtain ⟨p, hp, he⟩ := vdeg_update hf j (roundPoint ch j 0 tail)
    exact ⟨p, hp, fun x => by rw [he x, ← roundPoint_update]⟩
  choose q hq using hex
  obtain ⟨P, hP, hPe⟩ : ∃ P : K[X], P.natDegree < 28 ∧
      ∀ x, P.eval x = ∑ tail : Fin (9-j.val) → Bool, f (roundPoint ch j x tail) := by
    refine ⟨∑ tail, q tail, ?_, ?_⟩
    · exact Nat.lt_of_le_of_lt
        (natDegree_sum_le_of_forall_le _ _ (fun tail _ => (hq tail).1)) (by norm_num)
    · intro x
      rw [eval_finsetSum]
      exact Finset.sum_congr rfl (fun tail _ => (hq tail).2 x)
  have hdeg : P.degree < ((Finset.univ : Finset (Fin 28)).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    by_cases h0 : P = 0
    · rw [h0, degree_zero]
      exact WithBot.bot_lt_coe _
    · exact (natDegree_lt_iff_degree_lt h0).mp hP
  have hint : PayloadSplit.rounds ch j f = P := by
    rw [PayloadSplit.rounds_apply, Lagrange.eq_interpolate (nodes_injOn (K := K)) hdeg]
    exact Lagrange.interpolate_eq_of_values_eq_on _ _ (fun k _ => (hPe (k.val : K)).symm)
  rw [hint, hPe]

theorem eval_rounds_nine (ch : Challenges K) (f : PayloadSplit.PointFunction K)
    (hf : VDeg 10 (fun _ => 27) f) : (PayloadSplit.rounds ch 9 f).eval (alpha ch 9) = f (alpha ch) := by
  have h0 : (9 : ℕ) - (9 : Fin 10).val = 0 := rfl
  haveI : IsEmpty (Fin (9 - (9 : Fin 10).val)) := ⟨fun i => Fin.elim0 (Fin.cast h0 i)⟩
  rw [rounds_eval_of_vdeg ch 9 f hf, Fintype.sum_unique, roundPoint_nine,
    Function.update_eq_self]

theorem evalRound9_roundInclusion_rounds (ch : Challenges K) (f : PayloadSplit.PointFunction K)
    (hf : VDeg 10 (fun _ => 27) f) :
    evalRound9 ch (PayloadSplit.roundInclusion (Bat := Bat) (fun j i => (PayloadSplit.rounds ch j f).coeff i.val)) =
      f (alpha ch) := by
  rw [evalRound9_roundInclusion]
  simp only [sum_monomial_coeff _ (rounds_natDegree_lt ch 9 f), eval_rounds_nine ch f hf]

/-! ### Item 2: Φ₀ vanishes on the mask image -/

section LRead
attribute [local irreducible] claimsLinear extraLinear dotLinear honestClaims

theorem L_pointClaim (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (u : Trace K) (j : Fin 3) (c : Fin 29) :
    PayloadSplit.L (Bat := Bat) π B ch u (.pointClaim j c) = honestClaims u (alpha ch) j c := by
  simp only [PayloadSplit.L, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    linearPayload, claimsLinear_apply]

theorem L_extraClaim (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (u : Trace K) (c : Fin 29) :
    PayloadSplit.L (Bat := Bat) π B ch u (.extraClaim c) = R0P.Mask.honestExtra π u (alpha ch) c := by
  simp only [PayloadSplit.L, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    linearPayload, extraLinear_apply]

end LRead

theorem maskLinear_vdeg (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (u : Trace K) :
    VDeg 10 (fun _ => 27) (fun a => PayloadSplit.maskLinear π B a u) := by
  have hfun : (fun a => PayloadSplit.maskLinear π B a u) = fun a =>
      R0P.Mask.maskClaimsR0 B (honestClaims u a 0)
        (fun l => AspisR0.RoundNormalization.dot (SemSource.libraWeight a) (coeffsOf π u l)) a := by
    funext a
    rw [PayloadSplit.maskLinear_apply]
    rfl
  rw [hfun]
  exact R0P.Mask.maskClaimsR0_vdeg B π u

theorem Phi0_L (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (u : Trace K) :
    Phi0 B ch (PayloadSplit.L (Bat := Bat) π B ch u) = 0 := by
  have hround : round9Poly (PayloadSplit.L (Bat := Bat) π B ch u) =
      PayloadSplit.rounds ch 9 (fun a => PayloadSplit.maskLinear π B a u) := by
    rw [round9Poly_apply]
    simp only [PayloadSplit.L_round]
    exact sum_monomial_coeff _ (rounds_natDegree_lt ch 9 _)
  have h9 : evalRound9 ch (PayloadSplit.L (Bat := Bat) π B ch u) = PayloadSplit.maskLinear π B (alpha ch) u := by
    rw [evalRound9_apply, hround, eval_rounds_nine ch _ (maskLinear_vdeg π B u)]
  have hc : claimMask B (alpha ch) (PayloadSplit.L (Bat := Bat) π B ch u) =
      PayloadSplit.maskLinear π B (alpha ch) u := by
    rw [claimMask_apply, PayloadSplit.maskLinear_apply]
    simp only [L_pointClaim, L_extraClaim]
    rfl
  simp only [Phi0, LinearMap.sub_apply, h9, hc, sub_self]

/-- D17.2 item 2: silent masks lie in `ker Φ₀`. -/
theorem Phi0_A (h : HonestProver K) (B : PackBasis F) (ch : Challenges K) (t : T K F) :
    Phi0 B ch (A (Bat := Bat) h.transport B ch t) = 0 := by
  have hA : A (Bat := Bat) h.transport B ch t = PayloadSplit.L h.transport B ch (JointTrace.tapeLinear B t) := rfl
  rw [hA]
  exact Phi0_L h.transport B ch _

/-! ### Item 3: Φ₀ of the original round remainder -/

/-- The original terminal's point function at the prepared trace `t`. -/
def fOrig (pub : Public K) (B : PackBasis F) (ch : Challenges K) (t : Trace K) :
    PayloadSplit.PointFunction K :=
  fun a => ch.sem 14 * terminalValue pub (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B
    (honestClaims t a) a

theorem vdeg_fOrig (pub : Public K) (B : PackBasis F) (ch : Challenges K) (t : Trace K) :
    VDeg 10 (fun _ => 27) (fOrig pub B ch t) :=
  vdeg_smul (ch.sem 14)
    (vdeg_terminalValue pub t (ch.sem 0) (ch.sem 1) (ch.sem 2) (ch.sem 13) (zc ch) B)

theorem originalRounds_eq (pub : Public K) (B : PackBasis F) (ch : Challenges K) (t : Trace K) :
    PayloadSplit.originalRounds pub B ch t =
      fun j i => (PayloadSplit.rounds ch j (fOrig pub B ch t)).coeff i.val := rfl

theorem evalRound9_originalRounds (pub : Public K) (B : PackBasis F) (ch : Challenges K)
    (t : Trace K) :
    evalRound9 ch (PayloadSplit.roundInclusion (Bat := Bat) (PayloadSplit.originalRounds pub B ch t)) =
      fOrig pub B ch t (alpha ch) := by
  rw [originalRounds_eq]
  exact evalRound9_roundInclusion_rounds ch (fOrig pub B ch t) (vdeg_fOrig pub B ch t)

theorem payload_pointClaim (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (r : T K F) (j : Fin 3) (c : Fin 29) :
    payload (Bat := Bat) h B x w ch r (.pointClaim j c) =
      honestClaims (PayloadSplit.actual x.1 B (h.build w) ch r) (alpha ch) j c := rfl

theorem originalOf_payload (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (r : T K F) :
    originalOf x.1 B ch (payload (Bat := Bat) h B x w ch r) =
      fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch r) (alpha ch) := rfl

theorem originalOf_c (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) :
    originalOf x.1 B ch (c (Bat := Bat) h B x w ch) =
      fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch 0) (alpha ch) := by
  have hz : payload (Bat := Bat) h B x w ch 0 = c h B x w ch :=
    congrArg (JointView.payload h B x w ch) (map_zero Partition.equiv)
  rw [← hz]
  exact originalOf_payload h B x w ch 0

/-- D17.2 item 3. -/
theorem Phi0_roundInclusion_g (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K) (n : N K F) :
    Phi0 B ch (roundInclusion (F := F) (Bat := Bat) (g h B x w ch n)) =
      originalOf x.1 B ch (payload (Bat := Bat) h B x w ch (0,n)) - originalOf x.1 B ch (c (Bat := Bat) h B x w ch) := by
  have hg : roundInclusion (F := F) (Bat := Bat) (g h B x w ch n) =
      PayloadSplit.roundInclusion (PayloadSplit.originalRounds x.1 B ch
        (PayloadSplit.actual x.1 B (h.build w) ch (0,n))) -
      PayloadSplit.roundInclusion (PayloadSplit.originalRounds x.1 B ch
        (PayloadSplit.actual x.1 B (h.build w) ch 0)) :=
    map_sub PayloadSplit.roundInclusion _ _
  rw [hg, map_sub, Phi0_roundInclusion, Phi0_roundInclusion, evalRound9_originalRounds,
    evalRound9_originalRounds, originalOf_payload, originalOf_c]

/-! ### Item 4: the remainder has zero Φ₀ off alpha 9 = ½ -/

/-- D17.2 item 4. -/
theorem Phi0_sRem (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (n : N K F) (hgood : alpha ch 9 ≠ 1/2) :
    Phi0 B ch (sRem (Bat := Bat) h B x w ch n) = 0 := by
  unfold sRem
  rw [map_sub, map_smul, smul_eq_mul, Phi0_dir]
  have hne : alpha ch 9 - 1/2 ≠ 0 := sub_ne_zero.mpr hgood
  rw [mul_assoc, inv_mul_cancel₀ hne, mul_one, sub_self]

/-! ### Item 5: the shifted decomposition -/

theorem originalOf_payload_pure (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K) (m : M K F) (n : N K F) :
    originalOf x.1 B ch (payload (Bat := Bat) h B x w ch (m,n)) =
      originalOf x.1 B ch (payload (Bat := Bat) h B x w ch (0,n)) := by
  rw [originalOf_payload, originalOf_payload]
  unfold fOrig
  rw [PayloadSplit.actual_add_pure, PayloadSplit.terminal_add_pure]

/-- D17.2 item 5: the three `(alpha ch 9 − 1/2)⁻¹` terms cancel identically,
so no `Good` hypothesis is needed. -/
theorem payload_eq_shift (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (t : T K F) :
    payload (Bat := Bat) h B x w ch t =
      shift x.1 B ch (cTilde h B x w ch + A h.transport B ch t + sRem h B x w ch t.2) := by
  obtain ⟨m, n⟩ := t
  show payload (Bat := Bat) h B x w ch (m,n) =
    shift x.1 B ch (cTilde h B x w ch + A h.transport B ch (m,n) + sRem h B x w ch n)
  set κ := (alpha ch 9 - 1/2)⁻¹ with hκ
  have hdec : payload (Bat := Bat) h B x w ch (m,n) = c h B x w ch + A h.transport B ch (m,n) +
      roundInclusion (F := F) (g h B x w ch n) := decomposition h B x w ch (m,n)
  have hphi := Phi0_roundInclusion_g (Bat := Bat) h B x w ch n
  have hpure := originalOf_payload_pure (Bat := Bat) h B x w ch m n
  have hV : cTilde (Bat := Bat) h B x w ch + A h.transport B ch (m,n) + sRem h B x w ch n =
      payload h B x w ch (m,n) -
        (originalOf x.1 B ch (payload (Bat := Bat) h B x w ch (m,n)) * κ) • dir := by
    rw [hpure, hdec]
    unfold cTilde sRem
    rw [hphi]
    have hab : originalOf x.1 B ch (c (Bat := Bat) h B x w ch) * κ +
        (originalOf x.1 B ch (payload (Bat := Bat) h B x w ch (0,n)) - originalOf x.1 B ch (c (Bat := Bat) h B x w ch)) * κ =
        originalOf x.1 B ch (payload (Bat := Bat) h B x w ch (0,n)) * κ := by ring
    rw [← hab, add_smul]
    abel
  rw [hV]
  unfold shift
  rw [originalOf_sub_smul_dir, sub_add_cancel]

/-! ### Items 6–7: law transport through Ψ_ch and perfect HVZK on `Good` -/

/-- D17.2 item 6: equal laws are preserved by every observation. -/
theorem equalLaws_comp {R S V W : Type} [Fintype R] [Fintype S] (Ψ : V → W) {f : R → V}
    {g : S → V} (h : EqualLaws f g) : EqualLaws (Ψ ∘ f) (Ψ ∘ g) := by
  intro w
  exact LawTransport.mean_eq_of_equalLaws f g (fun v => if Ψ v = w then (1 : ℚ) else 0) h

/-- Perfect HVZK restricted to the challenges satisfying `P`. -/
def HVZK_on (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) : Prop :=
  ∀ (hx : JointView.InLanguage h x) (w : h.Instance) (ch : Challenges K), P ch →
    h.public w = x.1 →
    EqualLaws (JointView.view (Bat := Bat) h B outputs x w ch) (JointView.simulator h B outputs x hx ch)

/-- Clause (i′) at one challenge: the honest payload law is the shifted common coset law. -/
theorem payload_law_on [Fintype Bat] (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K)
    (hi : ∀ n, sRem (Bat := Bat) h B x w ch n ∈ LinearMap.range ((A h.transport B ch).comp inlM)) :
    EqualLaws (payload (Bat := Bat) h B x w ch)
      (fun t => shift x.1 B ch (cTilde h B x w ch + A h.transport B ch t)) := by
  have hmix := AbsorptionLaw.mixture (A h.transport B ch) (cTilde h B x w ch)
    (fun n => sRem h B x w ch n) hi
  have hcomp := equalLaws_comp (shift x.1 B ch) hmix
  have hfun : (shift x.1 B ch ∘ fun t : T K F =>
      cTilde h B x w ch + A h.transport B ch t + sRem h B x w ch t.2) = payload (Bat := Bat) h B x w ch := by
    funext t
    exact (payload_eq_shift h B x w ch t).symm
  rw [hfun] at hcomp
  exact hcomp

attribute [local irreducible] JointView.payload A g

/-- D17.2 item 7: D12's proof with `payload_eq_shift` in place of `decomposition`
and `equalLaws_comp (shift …)` after each law equality. -/
theorem hvzk_on_good [Fintype Bat] (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) :
    MaskImageOn (Bat := Bat) Good h B x → HVZK_on (Bat := Bat) Good h B outputs x := by
  intro hm hx w ch hgood hw
  let w' := Classical.choose hx
  have hw' : h.public w' = x.1 := Classical.choose_spec hx
  have hlaw := payload_law_on h B x w ch (fun n => hm.1 ch hgood w n hw)
  have hlaw' := payload_law_on h B x w' ch (fun n => hm.1 ch hgood w' n hw')
  have hlinear := AffineLaw.equal_laws_of_mask_image (A h.transport B ch) (A h.transport B ch)
    (cTilde h B x w ch) (cTilde h B x w' ch) rfl (hm.2 ch hgood w w' hw hw')
  have hshift := equalLaws_comp (shift x.1 B ch) hlinear
  have hpart : EqualLaws (payload (Bat := Bat) h B x w ch) (payload h B x w' ch) := by
    intro v
    exact (hlaw v).trans ((hshift v).trans (hlaw' v).symm)
  have hold : EqualLaws (JointView.payload (Bat := Bat) h B x w ch) (JointView.payload h B x w' ch) := by
    apply AbsorptionLaw.equal_laws_of_equiv Partition.equiv.toEquiv
    unfold R0Z.D12.payload at hpart
    exact hpart
  have hp := AffineLaw.equal_laws_const_pair (JointView.payload (Bat := Bat) h B x w ch)
    (JointView.payload h B x w' ch) (ZkStatement.metadata outputs x ch) hold
  unfold JointView.simulator JointView.view
  dsimp only [w'] at hp
  exact hp

/-- `hvzk_on_good` for an arbitrary challenge predicate `P` (job R1-0): the
proof never reads `Good` except to feed the mask-image clauses. -/
theorem hvzk_on_of [Fintype Bat] (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) :
    MaskImageOn (Bat := Bat) P h B x → HVZK_on (Bat := Bat) P h B outputs x := by
  intro hm hx w ch hP hw
  let w' := Classical.choose hx
  have hw' : h.public w' = x.1 := Classical.choose_spec hx
  have hlaw := payload_law_on h B x w ch (fun n => hm.1 ch hP w n hw)
  have hlaw' := payload_law_on h B x w' ch (fun n => hm.1 ch hP w' n hw')
  have hlinear := AffineLaw.equal_laws_of_mask_image (A h.transport B ch) (A h.transport B ch)
    (cTilde h B x w ch) (cTilde h B x w' ch) rfl (hm.2 ch hP w w' hw hw')
  have hshift := equalLaws_comp (shift x.1 B ch) hlinear
  have hpart : EqualLaws (payload (Bat := Bat) h B x w ch) (payload h B x w' ch) := by
    intro v
    exact (hlaw v).trans ((hshift v).trans (hlaw' v).symm)
  have hold : EqualLaws (JointView.payload (Bat := Bat) h B x w ch) (JointView.payload h B x w' ch) := by
    apply AbsorptionLaw.equal_laws_of_equiv Partition.equiv.toEquiv
    unfold R0Z.D12.payload at hpart
    exact hpart
  have hp := AffineLaw.equal_laws_const_pair (JointView.payload (Bat := Bat) h B x w ch)
    (JointView.payload h B x w' ch) (ZkStatement.metadata outputs x ch) hold
  unfold JointView.simulator JointView.view
  dsimp only [w'] at hp
  exact hp

#print MaskImageOn
#print HVZK_on
#print axioms rounds_eval_of_vdeg
#print axioms Phi0_A
#print axioms Phi0_roundInclusion_g
#print axioms Phi0_sRem
#print axioms payload_eq_shift
#print axioms equalLaws_comp
#print axioms hvzk_on_good
#print axioms hvzk_on_of
end R0Z.Shift
