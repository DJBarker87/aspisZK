import AspisV8R19.R707FullActiveDeterminant
import AspisV8R17.ActiveEntry
import AspisV8R17.MinorDegree
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R710SelectedActivePolynomial
open AspisV8R17 R702ActiveScalarEmbedding R698ActiveCoreLayout R707FullActiveDeterminant
open MvPolynomial
noncomputable section
variable {F : Type*} [Field F]
abbrev J := High ⊕ Unit

def columnIndex : J → Fin 699
  | .inl j => selectedColumn j
  | .inr _ => extraTopColumn

def base (j : J) : Nat := 4*(22+(columnIndex j).val/3)
def slot (j : J) : Nat := 1+(columnIndex j).val%3

def entry (half : F) (i j : J) : ActivePoly F :=
  activeEntry (sourceBasisConstants half (unitVector (base j+slot j)) (rowCode i))
    (sourceBasisConstants half (unitVector (base j)) (rowCode i)) (slot j)

def polyMinor (half : F) : Matrix J J (ActivePoly F) := entry half

def sourceMinor (half alpha a b c : F) : Matrix J J F := fun i j =>
  sourceChord half (fun r => unitVector (base j+slot j) r-alpha^slot j*unitVector (base j) r)
    a b c (rowCode i)

lemma entry_eval (half alpha u v : F) (i j : J) :
    eval (activeAssignment alpha u v) (entry half i j) =
      sourceMinor half alpha (1+u*v) (u*v-1) (-(u+v)) i j :=
  sourceEntry_eval _ _ _ _ _ _ _ _

lemma minor_eval (half alpha u v : F) :
    (eval (activeAssignment alpha u v)).mapMatrix (polyMinor half) =
      sourceMinor half alpha (1+u*v) (u*v-1) (-(u+v)) := by
  apply Matrix.ext
  intro i j
  exact entry_eval half alpha u v i j

lemma determinant_eval (half alpha u v : F) :
    eval (activeAssignment alpha u v) (polyMinor half).det =
      (sourceMinor half alpha (1+u*v) (u*v-1) (-(u+v))).det := by
  rw [(eval (activeAssignment alpha u v)).map_det,minor_eval]

lemma entry_degree (half : F) (i j : J) : (entry half i j).totalDegree ≤ 5 := by
  apply sourceEntry_degree
  have h := Nat.mod_lt (columnIndex j).val (by decide : 0<3)
  dsimp [slot]
  omega

lemma index_card : Fintype.card J = 214 := by
  rw [Fintype.card_sum]
  have hh : Fintype.card High=213 := by
    change Fintype.card {i : Fin 1024 // i ∈ highActive}=213
    rw [Fintype.card_coe,highActive_card]
  rw [hh]
  simp

lemma determinant_degree (half : F) : (polyMinor half).det.totalDegree ≤ 1070 := by
  have h := minor_totalDegree (polyMinor half) 5 (fun i j => entry_degree half i j)
  rw [index_card] at h
  exact h

#print axioms entry_eval
#print axioms determinant_eval
#print axioms entry_degree
#print axioms index_card
#print axioms determinant_degree
end
end AspisV8R19.R710SelectedActivePolynomial
