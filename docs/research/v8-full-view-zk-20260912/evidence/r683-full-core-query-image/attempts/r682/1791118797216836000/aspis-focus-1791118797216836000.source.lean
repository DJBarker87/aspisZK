import AspisV8R19.R679GeneralResidualMoments
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R682FullQueryNormalization
open AspisR19 AspisV8R17 AspisCircleTensorBinding
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]
def extendLow256 (r : Fin 22 → F) (i : Fin 256) : F :=
  if h : i.val < 22 then r ⟨i.val,h⟩ else 0

theorem extendLow256_sum (r : Fin 22 → F) (w : Fin 256 → F) :
    ∑ i, extendLow256 r i*w i = ∑ j : Fin 22, r j*w ⟨j.val,by omega⟩ := by
  rw [Fin.sum_univ_add (a:=22) (b:=234)]
  simp [extendLow256, Fin.castAdd, Fin.natAdd, Fin.castLE]

def evaluate256 (v : Fin 256 → F) (x : F) : F :=
  ∑ d, v d*naturalLineValue x d.val
#print axioms extendLow256_sum
end
end AspisV8R19.R682FullQueryNormalization
