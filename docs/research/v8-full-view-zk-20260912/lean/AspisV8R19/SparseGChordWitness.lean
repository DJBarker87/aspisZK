/- No new hiding assumption: bind the algebraic inverse to the retained
   source-shaped chord coefficient model, independent of scatter edges. -/
import AspisV8R17.SourceScatter
import AspisV8R19.SparseGCoreInverse

namespace AspisR19.SparseGChordWitness
open AspisV8R17 AspisR19.SparseGCoreInverse
variable {F : Type*} [CommRing F]

theorem scalar_chord (x xx : List (ScatterEdge Nat Nat F))
    (q : Nat → F) (a : F) (r : Nat) :
    chordCoefficient x xx q a 0 0 r = a*q r := by
  unfold chordCoefficient
  split
  · rename_i h
    have hr : 2*(r/2)=r := by omega
    simp only [chordEven,mul_zero,zero_mul,add_zero,hr]
  · rename_i h
    have hr : 2*(r/2)+1=r := by omega
    simp only [chordOdd,mul_zero,zero_mul,zero_add,add_zero,hr]

def sourceCore (x xx : List (ScatterEdge Nat Nat F)) (a b c : F)
    (v : Fin 271 → F) (i : Fin 271) : F :=
  chordCoefficient x xx (quotient (extend v)) a b c (128+3*i.val)

theorem sourceCore_scalar (x xx : List (ScatterEdge Nat Nat F))
    (a : F) (v : Fin 271 → F) (i : Fin 271) :
    sourceCore x xx a 0 0 v i = a*finiteBlock v i := by
  simp only [sourceCore,scalar_chord,source_block,finiteBlock]

theorem normalized_source_inverse (x xx : List (ScatterEdge Nat Nat F))
    (u h : F) (hu : u*u = -1) (hh : (2:F)*h=1) (v : Fin 271 → F) :
    sourceCore x xx (1+u*(-u)) (u*(-u)-1) (-(u+(-u)))
      (fun j => h*finiteBlock v j) = v := by
  have hp : u*(-u)=1 := by rw [mul_neg,hu,neg_neg]
  simp only [hp,sub_self,add_neg_cancel,neg_zero]
  have htwo : (1:F)+1=2 := by ring
  rw [htwo]
  funext i
  rw [sourceCore_scalar]
  exact congrFun (scaled_block_inverse h hh v) i

theorem normalized_source_surjective (x xx : List (ScatterEdge Nat Nat F))
    (u h : F) (hu : u*u = -1) (hh : (2:F)*h=1) :
    Function.Surjective (sourceCore x xx (1+u*(-u)) (u*(-u)-1) (-(u+(-u)))) := by
  intro v
  exact ⟨fun j => h*finiteBlock v j, normalized_source_inverse x xx u h hu hh v⟩

theorem normalized_source_injective (x xx : List (ScatterEdge Nat Nat F))
    (u h : F) (hu : u*u = -1) (hh : (2:F)*h=1) :
    Function.Injective (sourceCore x xx (1+u*(-u)) (u*(-u)-1) (-(u+(-u)))) := by
  have hp : u*(-u)=1 := by rw [mul_neg,hu,neg_neg]
  simp only [hp,sub_self,add_neg_cancel,neg_zero]
  intro v w he
  apply finite_bijective.1
  funext i
  have he' := congrFun he i
  rw [sourceCore_scalar,sourceCore_scalar] at he'
  have htwo : (1:F)+1=2 := by ring
  rw [htwo] at he'
  have he'' := congrArg (fun t => h*t) he'
  simpa only [← mul_assoc,mul_comm h (2:F),hh,one_mul] using he''

#print axioms scalar_chord
#print axioms sourceCore_scalar
#print axioms normalized_source_inverse
#print axioms normalized_source_surjective
#print axioms normalized_source_injective
end AspisR19.SparseGChordWitness
