import AspisV8R19.QM31NormalizedSection
import AspisV8R19.NormalizedGCore

/-! Exact scope: the fixed algebraic specialization, every injective root
tuple, source-shaped natural evaluation/fold/chord, all 271 G reads.
Not a theorem about an accepted source prefix or its distribution. -/
namespace AspisR19.NormalizedSectionBoundary
open AspisV8R15.ExactTowerBase QM31ResidualWitness QM31NormalizedSection
open NormalizedQuerySection NormalizedGCore
noncomputable section
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hz : (2 : RootCertificate.M)=0 := by
    apply embed_injective
    simpa only [map_ofNat,map_zero] using h
  exact (by decide : (2 : RootCertificate.M) ≠ 0) hz⟩

theorem columns_g_zero (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (half a b c : QM31Exact) (j : Fin 13) (i : Fin 271) :
    AspisV8R17.sourceChord half (flatten (columns t ht j)) a b c (128+3*i.val)=0 :=
  normalized_selected_g_zero t ht half (embed 7) a b c j i

theorem columns_raw_zero (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (j : Fin 13) (r : Fin 22) (x y : QM31Exact) :
    let a := evaluate (fun i => columns t ht j (i,0)) (t r)
    let b := evaluate (fun i => columns t ht j (i,1)) (t r)
    let c := evaluate (fun i => columns t ht j (i,2)) (t r)
    let d := evaluate (fun i => columns t ht j (i,3)) (t r)
    a+b*y+c*x+d*x*y=0 ∧ a-b*y+c*x-d*x*y=0 ∧
    a-b*y-c*x+d*x*y=0 ∧ a+b*y-c*x-d*x*y=0 := by
  dsimp only
  simp only [columns_root_zero]
  simp

theorem columns_final_zero (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (j : Fin 13) (z x y : QM31Exact) (hx : x ≠ 0) (hy : y ≠ 0) :
    let a := evaluate (fun i => columns t ht j (i,0)) z
    let b := evaluate (fun i => columns t ht j (i,1)) z
    let c := evaluate (fun i => columns t ht j (i,2)) z
    let d := evaluate (fun i => columns t ht j (i,3)) z
    AspisV8R16.foldFour x y (embed 7)
      (a+b*y+c*x+d*x*y) (a-b*y+c*x-d*x*y)
      (a-b*y-c*x+d*x*y) (a+b*y-c*x-d*x*y)=0 := by
  exact NormalizedQuotient.final_zero_of_coefficients (columns t ht j) (embed 7)
    (columns_fold_zero t ht j) z x y hx hy

theorem fixed_query_section (t : Fin 22 → QM31Exact) (ht : Function.Injective t) :
    (matrix t ht).det ≠ 0 ∧
    (∀ j k r, evaluate (fun i => columns t ht j (i,k)) (t r)=0) ∧
    (∀ j i, ∑ k : Fin 4, (embed 7)^k.val * columns t ht j (i,k)=0) ∧
    (∀ half a b c j i, AspisV8R17.sourceChord half (flatten (columns t ht j))
      a b c (128+3*(i : Fin 271).val)=0) :=
  ⟨det_ne_zero t ht,columns_root_zero t ht,columns_fold_zero t ht,columns_g_zero t ht⟩

#print axioms columns_g_zero
#print axioms columns_raw_zero
#print axioms columns_final_zero
#print axioms fixed_query_section
end
end AspisR19.NormalizedSectionBoundary
