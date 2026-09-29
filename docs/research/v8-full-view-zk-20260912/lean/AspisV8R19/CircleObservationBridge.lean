import AspisV8R19.CircleChannelsBridge

namespace AspisR19.CircleObservationBridge
open AspisV8R16 AspisCircleTensorBinding HighRepairInvariant
open SourceEncodedOpening SourceMaskTransport SourceChordEvaluation NormalizedGCore CircleChannelsBridge
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem doubled_neg (x : F) : doubledFactor (-x) 1=doubledFactor x 1 := by
  simp [doubledFactor]

theorem fibre_values (q : Index 32 → F) (x y : F) :
    let a := NormalizedQuerySection.evaluate (fun i => q (i,0)) (doubledFactor x 1)
    let b := NormalizedQuerySection.evaluate (fun i => q (i,1)) (doubledFactor x 1)
    let c := NormalizedQuerySection.evaluate (fun i => q (i,2)) (doubledFactor x 1)
    let d := NormalizedQuerySection.evaluate (fun i => q (i,3)) (doubledFactor x 1)
    sourceEvaluate (flatten q) x y=a+b*y+c*x+d*x*y ∧
    sourceEvaluate (flatten q) x (-y)=a-b*y+c*x-d*x*y ∧
    sourceEvaluate (flatten q) (-x) (-y)=a-b*y-c*x+d*x*y ∧
    sourceEvaluate (flatten q) (-x) y=a+b*y-c*x-d*x*y := by
  simp only [sourceEvaluate_channels,doubled_neg,channels]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem quotient_fold_zero (q : Index 32 → F) (alpha : F)
    (hq : ∀ i, ∑ k : Fin 4, alpha^k.val*q (i,k)=0)
    (x y : F) (hx : x≠0) (hy : y≠0) :
    foldFour x y alpha (sourceEvaluate (flatten q) x y) (sourceEvaluate (flatten q) x (-y))
      (sourceEvaluate (flatten q) (-x) (-y)) (sourceEvaluate (flatten q) (-x) y)=0 := by
  obtain ⟨h0,h1,h2,h3⟩ := fibre_values q x y
  rw [h0,h1,h2,h3]
  exact NormalizedQuotient.final_zero_of_coefficients q alpha hq (doubledFactor x 1) x y hx hy

def sourceMaskEvaluate (m : Fin 1024 → F) (x y : F) : F :=
  sourceEvaluate (fun r => if h : r<1024 then
    transport T163SourceTable.inactive 1023 T163SourceTable.order m ⟨r,h⟩ else 0) x y

theorem sourceMaskEvaluate_eq (m : Fin 1024 → F) (x y : F) :
    sourceMaskEvaluate m x y=encodedOpening m x y := by
  exact sourceEvaluate_eq _ x y

theorem mask_point (q : Index 32 → F) (a b c x y : F) (circle : x^2+y^2=1) :
    sourceMaskEvaluate (mask (2:F)⁻¹ a b c q) x y=
      (a+b*x+c*y)*sourceEvaluate (flatten q) x y := by
  rw [sourceMaskEvaluate_eq,mask_opening q a b c x y circle,input_channels,sourceEvaluate_channels]

theorem mask_root_zero (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (d : Fin 32) (s : Fin 4) (j : Fin 22) (a b c x y : F)
    (circle : x^2+y^2=1) (root : doubledFactor x 1=t j) :
    sourceMaskEvaluate (mask (2:F)⁻¹ a b c (NormalizedQuotient.quotient t ht alpha d s)) x y=0 := by
  rw [mask_point _ a b c x y circle,source_quotient_root t ht alpha d s j x y root,mul_zero]

theorem mask_division (q : Index 32 → F) (a b c x y : F)
    (circle : x^2+y^2=1) (line_ne : a+b*x+c*y≠0) :
    sourceMaskEvaluate (mask (2:F)⁻¹ a b c q) x y/(a+b*x+c*y)=sourceEvaluate (flatten q) x y := by
  rw [mask_point q a b c x y circle]
  exact mul_div_cancel_left₀ _ line_ne

theorem mask_division_fold_zero (q : Index 32 → F) (alpha : F)
    (hq : ∀ i, ∑ k : Fin 4, alpha^k.val*q (i,k)=0)
    (a b c x y : F) (circle : x^2+y^2=1) (hx : x≠0) (hy : y≠0)
    (l0 : a+b*x+c*y≠0) (l1 : a+b*x+c*(-y)≠0)
    (l2 : a+b*(-x)+c*(-y)≠0) (l3 : a+b*(-x)+c*y≠0) :
    let m := mask (2:F)⁻¹ a b c q
    foldFour x y alpha
      (sourceMaskEvaluate m x y/(a+b*x+c*y))
      (sourceMaskEvaluate m x (-y)/(a+b*x+c*(-y)))
      (sourceMaskEvaluate m (-x) (-y)/(a+b*(-x)+c*(-y)))
      (sourceMaskEvaluate m (-x) y/(a+b*(-x)+c*y))=0 := by
  dsimp only
  rw [mask_division q a b c x y circle l0,
    mask_division q a b c x (-y) (by simpa using circle) l1,
    mask_division q a b c (-x) (-y) (by simpa using circle) l2,
    mask_division q a b c (-x) y (by simpa using circle) l3]
  exact quotient_fold_zero q alpha hq x y hx hy

#print axioms doubled_neg
#print axioms fibre_values
#print axioms quotient_fold_zero
#print axioms sourceMaskEvaluate_eq
#print axioms mask_point
#print axioms mask_root_zero
#print axioms mask_division
#print axioms mask_division_fold_zero
end
end AspisR19.CircleObservationBridge
