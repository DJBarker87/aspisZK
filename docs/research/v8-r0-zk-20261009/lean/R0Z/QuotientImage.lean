import R0Z.HonestView
import R0Z.KernelImage
import R0P.CircleSampler

/-! D10: the exact chord quotient is on the encoder image for distinct
non-base-rational endpoints. Rank-nullity is symbolic; the million-symbol
domain and the finite field are never enumerated. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.HonestView
open R0P.SemSource AspisR0.Chord AspisR0.ChordImage AspisR0.ChordGeometry
open AspisWide.InitialEncoder AspisWide.Agreement
open AspisPool.AlgorithmicCircleDecoderV7
attribute [local instance] Classical.propDecidable
attribute [local irreducible] exactInitialEncoder chordMessage interpolant exactInitialLinear oodLinear

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def endpointLinear (z0 z1 : Point K) : InitialMessage K →ₗ[K] K × K :=
  (oodLinear z0).prod (oodLinear z1)

def imageConstraints (z0 z1 : Point K) : InitialMessage K →ₗ[K] K × K :=
  e1.prod (e2 (secantB z0 z1) (secantC z0 z1))

theorem endpointLinear_surjective (z0 z1 : Point K) (hz : z0 ≠ z1) :
    Function.Surjective (endpointLinear z0 z1) := by
  intro y
  let v : Fin 2 → K := fun i => if i = 0 then y.1 else y.2
  refine ⟨interpolant z0 z1 v, ?_⟩
  have hv := interpolant_values z0 z1 hz v
  apply Prod.ext <;>
    simp only [endpointLinear, LinearMap.prod_apply, Function.prod, oodLinear_apply,
      hv.1, hv.2, v, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]

def chordOnKernel (z0 z1 : Point K) (hz : z0 ≠ z1) :
    LinearMap.ker (imageConstraints z0 z1) →ₗ[K] LinearMap.ker (endpointLinear z0 z1) :=
  LinearMap.codRestrict _
    ((chordLinear (secantA z0 z1) (secantB z0 z1) (secantC z0 z1)).comp
      (LinearMap.ker (imageConstraints z0 z1)).subtype) (by
    intro q
    have hq : e1 q.1 = 0 ∧ e2 (secantB z0 z1) (secantC z0 z1) q.1 = 0 :=
      Prod.mk.inj q.2
    change endpointLinear z0 z1 (chordMessage _ _ _ q.1) = 0
    apply Prod.ext <;>
      simp only [endpointLinear, LinearMap.prod_apply, Function.prod, oodLinear_apply,
        product_eval z0 z1 hz q.1 hq.1 hq.2,
        (secant_zeroes z0 z1).1, (secant_zeroes z0 z1).2, zero_mul, Prod.fst_zero, Prod.snd_zero])

theorem chordOnKernel_injective (z0 z1 : Point K) (hz : z0 ≠ z1)
    (h0 : ¬ BaseRational z0) (h1 : ¬ BaseRational z1) :
    Function.Injective (chordOnKernel z0 z1 hz) := by
  intro q r he
  have hq : e1 q.1 = 0 ∧ e2 (secantB z0 z1) (secantC z0 z1) q.1 = 0 := Prod.mk.inj q.2
  have hr : e1 r.1 = 0 ∧ e2 (secantB z0 z1) (secantC z0 z1) r.1 = 0 := Prod.mk.inj r.2
  have hc : chordMessage (secantA z0 z1) (secantB z0 z1) (secantC z0 z1) q.1 =
      chordMessage (secantA z0 z1) (secantB z0 z1) (secantC z0 z1) r.1 :=
    by
      have he' := congrArg (fun v : LinearMap.ker (endpointLinear z0 z1) => v.1) he
      exact he'
  have hw := congrArg exactInitialEncoder hc
  rw [chordMessage_encoder _ _ _ (secant_nontrivial z0 z1 hz) _ hq.1 hq.2,
    chordMessage_encoder _ _ _ (secant_nontrivial z0 z1 hz) _ hr.1 hr.2] at hw
  apply Subtype.ext
  apply exactInitialEncoder_injective
  funext i
  exact mul_left_cancel₀ (no_domain_zero z0 z1 hz h0 h1 i) (congrFun hw i)

/-- The honest pointwise quotient before applying the total linear decoder. -/
def quotientWord (z0 z1 : Point K) (q : InitialMessage K) : InitialWord K :=
  fun i => (L z0 z1 i)⁻¹ * exactInitialEncoder
    (q - interpolant z0 z1 (fun j => evalMessage q (if j = 0 then z0 else z1))) i

theorem quotientLinear_eq_decode (z0 z1 : Point K) (q : InitialMessage K) :
    quotientLinear z0 z1 q = (exactInitialLinear (E := K)).leftInverse (quotientWord z0 z1 q) := by
  have hv : (LinearMap.pi fun j : Fin 2 => oodLinear (if j = 0 then z0 else z1)) q =
      (fun j => evalMessage q (if j = 0 then z0 else z1)) := by
    funext j
    exact oodLinear_apply _ _
  unfold quotientLinear
  rw [LinearMap.comp_apply]
  apply congrArg (exactInitialLinear (E := K)).leftInverse
  funext i
  simp only [LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.id_apply, smul_eq_mul,
    exactInitialLinear_apply, quotientWord]
  rw [hv]
  rfl

theorem quotient_mem_image_of_nonrational (z0 z1 : Point K) (q : InitialMessage K)
    (hz : z0 ≠ z1) (h0 : ¬ BaseRational z0) (h1 : ¬ BaseRational z1) :
    quotientWord z0 z1 q ∈ Set.range (exactInitialEncoder (K := K)) := by
  let y : Fin 2 → K := fun j => evalMessage q (if j = 0 then z0 else z1)
  let m := q - interpolant z0 z1 y
  have hm : m ∈ LinearMap.ker (endpointLinear z0 z1) := by
    have hy := interpolant_values z0 z1 hz y
    change endpointLinear z0 z1 (q - interpolant z0 z1 y) = 0
    rw [map_sub]
    apply Prod.ext <;>
      simp only [endpointLinear, LinearMap.prod_apply, Function.prod,
        oodLinear_apply, hy.1, hy.2, y, ite_true,
        if_neg (by decide : (1 : Fin 2) ≠ 0), sub_self, Prod.fst_zero, Prod.snd_zero]
  have hs := KernelImage.surjective (imageConstraints z0 z1) (endpointLinear z0 z1)
    (endpointLinear_surjective z0 z1 hz) (chordOnKernel z0 z1 hz)
    (chordOnKernel_injective z0 z1 hz h0 h1)
  obtain ⟨r, hr⟩ := hs ⟨m, hm⟩
  have hc : chordMessage (secantA z0 z1) (secantB z0 z1) (secantC z0 z1) r.1 = m :=
    by
      have hr' := congrArg (fun v : LinearMap.ker (endpointLinear z0 z1) => v.1) hr
      exact hr'
  have hri : e1 r.1 = 0 ∧ e2 (secantB z0 z1) (secantC z0 z1) r.1 = 0 := Prod.mk.inj r.2
  have he := chordMessage_encoder (secantA z0 z1) (secantB z0 z1) (secantC z0 z1)
    (secant_nontrivial z0 z1 hz) r.1 hri.1 hri.2
  rw [hc] at he
  refine ⟨r.1, ?_⟩
  funext i
  change exactInitialEncoder r.1 i = (L z0 z1 i)⁻¹ * exactInitialEncoder m i
  rw [he]
  change _ = (L z0 z1 i)⁻¹ * (L z0 z1 i * exactInitialEncoder r.1 i)
  rw [inv_mul_cancel_left₀ (no_domain_zero z0 z1 hz h0 h1 i)]

/-- D10 for the actual two total circle samplers. Distinctness is the only
remaining premise; nonrationality follows from their accepted/fallback design. -/
theorem quotient_mem_image (s0 s1 : AspisV8R19.SourceDuplexStep.State)
    (q : InitialMessage AspisWideTower.WideExact)
    (hz : circleSample0 s0 ≠ circleSample1 s1) :
    quotientWord (circleSample0 s0) (circleSample1 s1) q ∈ Set.range exactInitialEncoder :=
  quotient_mem_image_of_nonrational _ _ q hz
    (circleSampleParameter0_not_rational _) (circleSampleParameter1_not_rational _)

/-- Any encoded preimage is the chosen decoder output, so that preimage is
unique regardless of how the left inverse was extended off the code. -/
theorem quotientLinear_eq_of_encode_eq (z0 z1 : Point K) (q r : InitialMessage K)
    (hr : exactInitialEncoder r = quotientWord z0 z1 q) : quotientLinear z0 z1 q = r := by
  rw [quotientLinear_eq_decode, ← hr, decode_encoded]

theorem quotientLinear_unique_preimage (s0 s1 : AspisV8R19.SourceDuplexStep.State)
    (q : InitialMessage AspisWideTower.WideExact)
    (hz : circleSample0 s0 ≠ circleSample1 s1) :
    ∃! r, exactInitialEncoder r = quotientWord (circleSample0 s0) (circleSample1 s1) q ∧
      quotientLinear (circleSample0 s0) (circleSample1 s1) q = r := by
  obtain ⟨r, hr⟩ := quotient_mem_image s0 s1 q hz
  refine ⟨r, ⟨hr, quotientLinear_eq_of_encode_eq _ _ q r hr⟩, ?_⟩
  intro r' hr'
  exact exactInitialEncoder_injective (hr'.1.trans hr.symm)

theorem quotient_off_image_only_eq (s0 s1 : AspisV8R19.SourceDuplexStep.State)
    (q : InitialMessage AspisWideTower.WideExact)
    (h : quotientWord (circleSample0 s0) (circleSample1 s1) q ∉ Set.range exactInitialEncoder) :
    circleSample1 s1 = circleSample0 s0 := by
  by_contra hz
  exact h (quotient_mem_image s0 s1 q (Ne.symm hz))

#print axioms quotient_mem_image_of_nonrational
#print axioms quotient_mem_image
#print axioms quotientLinear_unique_preimage
#print axioms quotient_off_image_only_eq
end R0Z.HonestView
