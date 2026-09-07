import AspisFormal.V5RankOneOpeningHiding

/-!
# V8 hiding must target the legal image, not the ambient product

The V8 public tuple can contain coordinates that are deterministically related.
The important example is a pair of component evaluations at Frobenius-conjugate
OOD points: for an M31-coefficient component the second value is the Frobenius
image of the first.  Such a pair is legal under the current Rust checks, so the
two-value map is not surjective onto the ambient product even though it need not
leak anything.

This file records the exact linear-algebra criterion needed by the V8 hiding
proof.  Every legal same-statement witness difference must be in the image of
the mask-view map.  Ambient surjectivity is sufficient but is not necessary.
The theorem is insensitive to duplicate or otherwise linearly dependent public
coordinates because arbitrary deterministic linear post-processing preserves
the image inclusion.
-/

open scoped ENNReal

namespace AspisV8A100HidingImageCriterion

variable {F Mask Witness View Observed : Type*}
variable [Field F]
variable [AddCommGroup Mask] [Module F Mask]
variable [AddCommGroup Witness] [Module F Witness]
variable [AddCommGroup View] [Module F View]
variable [AddCommGroup Observed] [Module F Observed]

/-- Translation of the finite mask space. -/
def maskTranslation (shift : Mask) : Mask ≃ Mask where
  toFun mask := mask + shift
  invFun mask := mask - shift
  left_inv mask := by simp
  right_inv mask := by simp

/-- A schedule-specific V8 hiding obligation.  This is deliberately image
containment, rather than surjectivity onto an ambient coordinate product. -/
def HidingImageObligation {Schedule : Type*}
    (legal : Schedule → Prop)
    (maskView : Schedule → Mask →ₗ[F] View)
    (witnessView : Schedule → Witness →ₗ[F] View) : Prop :=
  ∀ schedule, legal schedule →
    LinearMap.range (witnessView schedule) ≤ LinearMap.range (maskView schedule)

/-- One legal witness difference can be translated away exactly when its
public-view difference is in the mask image. -/
theorem exists_mask_translation
    (maskView : Mask →ₗ[F] View) (witnessView : Witness →ₗ[F] View)
    (himage : LinearMap.range witnessView ≤ LinearMap.range maskView)
    (left right : Witness) :
    ∃ shift : Mask, maskView shift = witnessView right - witnessView left := by
  have hmem : witnessView (right - left) ∈ LinearMap.range maskView :=
    himage (by exact ⟨right - left, rfl⟩)
  obtain ⟨shift, hshift⟩ := hmem
  refine ⟨shift, hshift.trans ?_⟩
  rw [map_sub]

/-- Exact uniform-law hiding from legal-image containment.  No rank claim on
the ambient `View` type is used. -/
theorem affine_view_pmf_eq_of_image_containment
    [Fintype Mask] [Nonempty Mask]
    (maskView : Mask →ₗ[F] View) (witnessView : Witness →ₗ[F] View)
    (himage : LinearMap.range witnessView ≤ LinearMap.range maskView)
    (left right : Witness) :
    (PMF.uniformOfFintype Mask).map
        (fun mask => witnessView left + maskView mask) =
      (PMF.uniformOfFintype Mask).map
        (fun mask => witnessView right + maskView mask) := by
  obtain ⟨shift, hshift⟩ :=
    exists_mask_translation maskView witnessView himage left right
  have hinvariant :
      (PMF.uniformOfFintype Mask).map (maskTranslation shift) =
        PMF.uniformOfFintype Mask :=
    AspisV5RankOneOpeningHiding.uniform_map_equiv (maskTranslation shift)
  calc
    (PMF.uniformOfFintype Mask).map
        (fun mask => witnessView left + maskView mask) =
        ((PMF.uniformOfFintype Mask).map (maskTranslation shift)).map
          (fun mask => witnessView left + maskView mask) := by rw [hinvariant]
    _ = (PMF.uniformOfFintype Mask).map
          (fun mask => witnessView left + maskView (mask + shift)) := by
            rw [PMF.map_comp]
            rfl
    _ = (PMF.uniformOfFintype Mask).map
          (fun mask => witnessView right + maskView mask) := by
            congr 1
            funext mask
            simp only [map_add, hshift]
            abel

/-- The schedule-indexed form needed by V8. -/
theorem v8_hiding_of_image_obligation
    {Schedule : Type*} [Fintype Mask] [Nonempty Mask]
    (legal : Schedule → Prop)
    (maskView : Schedule → Mask →ₗ[F] View)
    (witnessView : Schedule → Witness →ₗ[F] View)
    (hobligation : HidingImageObligation legal maskView witnessView)
    (schedule : Schedule) (hschedule : legal schedule)
    (left right : Witness) :
    (PMF.uniformOfFintype Mask).map
        (fun mask => witnessView schedule left + maskView schedule mask) =
      (PMF.uniformOfFintype Mask).map
        (fun mask => witnessView schedule right + maskView schedule mask) :=
  affine_view_pmf_eq_of_image_containment
    (maskView schedule) (witnessView schedule)
    (hobligation schedule hschedule) left right

/-- Deterministic linear observation (including duplicate coordinates, folds,
or a serialization projection) preserves the required image containment. -/
theorem image_containment_postcomp
    (maskView : Mask →ₗ[F] View) (witnessView : Witness →ₗ[F] View)
    (himage : LinearMap.range witnessView ≤ LinearMap.range maskView)
    (observe : View →ₗ[F] Observed) :
    LinearMap.range (observe.comp witnessView) ≤
      LinearMap.range (observe.comp maskView) := by
  rintro value ⟨witness, rfl⟩
  obtain ⟨mask, hmask⟩ := himage ⟨witness, rfl⟩
  exact ⟨mask, by simp only [LinearMap.comp_apply, hmask]⟩

section ConjugatePair

variable {K Source : Type*}
variable [Field K] [Module F K]
variable [AddCommGroup Source] [Module F Source]

/-- Abstract form of evaluating an F-coefficient component at one extension
point and at a conjugate point. -/
def conjugatePairView (evaluation : Source →ₗ[F] K) (sigma : K ≃ₗ[F] K) :
    Source →ₗ[F] K × K :=
  evaluation.prod (sigma.toLinearMap.comp evaluation)

/-- A conjugate pair is never surjective onto the ambient product: `(0,1)` is
outside its graph.  Therefore a V8 theorem demanding ambient full rank for
every distinct secure OOD pair is false as soon as the sampler admits a
Frobenius-conjugate pair. -/
theorem conjugatePairView_not_surjective
    (evaluation : Source →ₗ[F] K) (sigma : K ≃ₗ[F] K) :
    ¬ Function.Surjective (conjugatePairView evaluation sigma) := by
  intro hsurjective
  obtain ⟨source, hsource⟩ := hsurjective (0, 1)
  have hzero : evaluation source = 0 := congrArg Prod.fst hsource
  have hone : sigma (evaluation source) = 1 := congrArg Prod.snd hsource
  rw [hzero, map_zero] at hone
  exact zero_ne_one hone

/-- Despite failure of ambient surjectivity, a witness contribution using the
same conjugate-pair map is perfectly hidden by an independent uniform source
mask.  This is the duplicate/equality-safe shape required for V8. -/
theorem conjugatePairView_hides_its_legal_image
    [Fintype Source] [Nonempty Source]
    (evaluation : Source →ₗ[F] K) (sigma : K ≃ₗ[F] K)
    (left right : Source) :
    (PMF.uniformOfFintype Source).map
        (fun mask => conjugatePairView evaluation sigma left +
          conjugatePairView evaluation sigma mask) =
      (PMF.uniformOfFintype Source).map
        (fun mask => conjugatePairView evaluation sigma right +
          conjugatePairView evaluation sigma mask) := by
  apply affine_view_pmf_eq_of_image_containment
    (conjugatePairView evaluation sigma)
    (conjugatePairView evaluation sigma)
  exact le_rfl

end ConjugatePair

#print axioms affine_view_pmf_eq_of_image_containment
#print axioms v8_hiding_of_image_obligation
#print axioms image_containment_postcomp
#print axioms conjugatePairView_not_surjective
#print axioms conjugatePairView_hides_its_legal_image

end AspisV8A100HidingImageCriterion
