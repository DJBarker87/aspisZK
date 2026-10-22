import S4TailFieldProductRootV1
import S4OuterFoldTraceV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsHeadFieldAlgebraRootV1
open AspisR1FastDotsTailFieldProductRootV1
abbrev M := AspisR1FastDotsPushProductTraceRootV1.M
abbrev Contribution := AspisR1FastDotsActualTermTraceRootV1.Contribution

def decodeNat8 (f : Fin 8 → Nat) : TowerWide :=
  ⟨AspisV8R17.QM31WordTower.embedQ
      (((f ⟨0,by decide⟩ : M),(f ⟨1,by decide⟩ : M)),
       ((f ⟨2,by decide⟩ : M),(f ⟨3,by decide⟩ : M))),
   AspisV8R17.QM31WordTower.embedQ
      (((f ⟨4,by decide⟩ : M),(f ⟨5,by decide⟩ : M)),
       ((f ⟨6,by decide⟩ : M),(f ⟨7,by decide⟩ : M)))⟩

def embedM31 (n : Nat) : TowerWide := ⟨⟨⟨(n : M),0⟩,0⟩,0⟩

def contributionDecoded (c : Contribution) : TowerWide := decodeNat8 c.product

def sourceProduct (c : Contribution) : TowerWide :=
  wideDecoded c.wide * embedM31 c.scalar.val

/-- Source limb conversion suffices to identify the eight actual integer
products with a literal Wide-field multiplication by the base scalar. -/
theorem actual_contribution_decodes (c : Contribution)
    (hcoeff : AspisR1EbyKPushWideToQ.toLimbs c.wide = .ok c.coeff) :
    contributionDecoded c = sourceProduct c := by
  cases c with
  | mk term bytes scalar wide coeff =>
    change AspisR1EbyKPushWideToQ.toLimbs wide = .ok coeff at hcoeff
    unfold AspisR1EbyKPushWideToQ.toLimbs at hcoeff
    have heq := Result.ok.inj hcoeff
    subst coeff
    apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
      apply QuadraticAlgebra.ext <;>
      simp [contributionDecoded,decodeNat8,sourceProduct,embedM31,wideDecoded,qmDecoded,
        AspisR1FastDotsActualTermTraceRootV1.Contribution.product,
        AspisR1FastDotsActualLimbLoopExactRootV1.coeffCell,
        AspisR1FastDotsActualLimbExactStepRootV1.coeffCell,Array.make,
        AspisV8R17.QM31WordTower.decodeQ,AspisV8R17.QM31WordTower.decodeC,
        AspisV8R17.QM31WordTower.embedQ,AspisV8R17.QM31WordTower.embedC,
        AspisV8R17.QM31WordResidues.decodeQ,AspisV8R17.QM31WordResidues.decodeC,
        Nat.cast_mul] <;> rfl

theorem decodeNat8_add (f g : Fin 8 → Nat) :
    decodeNat8 (fun j=>f j+g j) = decodeNat8 f + decodeNat8 g := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    apply QuadraticAlgebra.ext <;>
    simp [decodeNat8,AspisV8R17.QM31WordTower.embedQ,
      AspisV8R17.QM31WordTower.embedC,Nat.cast_add] <;> rfl

theorem decodeNat8_sum {A : Type} (xs : List A) (f : A → Fin 8 → Nat) :
    decodeNat8 (fun j=>(xs.map (fun x=>f x j)).sum) =
      (xs.map (fun x=>decodeNat8 (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change decodeNat8 (fun j=>f x j+(xs.map (fun y=>f y j)).sum) =
      decodeNat8 (f x)+(xs.map (fun y=>decodeNat8 (f y))).sum
    rw [decodeNat8_add,ih]

#print axioms actual_contribution_decodes
#print axioms decodeNat8_add
#print axioms decodeNat8_sum
end AspisR1FastDotsHeadFieldAlgebraRootV1
