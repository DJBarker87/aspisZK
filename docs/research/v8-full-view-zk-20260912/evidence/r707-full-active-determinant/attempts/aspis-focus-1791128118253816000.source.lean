import AspisV8R19.R705HighChordDeterminant
import AspisV8R19.R706ExtraActiveColumn
import AspisV8R19.R704LastRowDeterminant
import AspisV8R19.R699SourceTopChordBoundary
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R707FullActiveDeterminant
open R702ActiveScalarEmbedding R705HighChordDeterminant R704LastRowDeterminant
open R699SourceTopChordBoundary AspisV8R17
noncomputable section
variable {F : Type*} [Field F]

def polyChord (half : F) (q : Nat → F) (r : Nat) : Polynomial F :=
  Polynomial.C (sourceChord half q 2 0 0 r) + Polynomial.X *
    Polynomial.C (sourceChord half q 0 0 1 r)

lemma polyChord_eval (half c : F) (q : Nat → F) (r : Nat) :
    (polyChord half q r).eval c = sourceChord half q 2 0 c r := by
  have hc := sourceChord_six_constants half q q 2 0 c 0 r
  have h0 := sourceChord_six_constants half q q 2 0 0 0 r
  simp only [zero_mul,sub_zero,mul_zero,add_zero] at hc h0
  simp only [polyChord,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
  rw [hc,h0]

lemma polyChord_top_pivot (half : F) (q : Nat → F) (h2 : (2:F) ≠ 0)
    (h22 : q 1022=0) (h23 : q 1023=0) :
    polyChord half q 1022 + (Polynomial.C (half/2)*Polynomial.X)*polyChord half q 1019 =
      (Polynomial.C (half/2)*Polynomial.X^2)*Polynomial.C (q 1018) := by
  have hh : (half/2)*2=half := div_mul_cancel₀ half h2
  have hp : Polynomial.C (half/2)*Polynomial.C (2:F)=Polynomial.C half := by
    rw [← Polynomial.C_mul,hh]
  simp only [polyChord,chord_top_even,chord_preceding_odd,h22,h23,mul_zero,
    zero_add,zero_mul,add_zero,one_mul,zero_sub,map_zero]
  simp only [map_neg,map_mul,map_zero]
  calc
    _ = -(Polynomial.C half * Polynomial.C (q 1019))*Polynomial.X +
        (Polynomial.C (half/2)*Polynomial.C (2:F))*Polynomial.C (q 1019)*Polynomial.X +
        Polynomial.C (half/2)*Polynomial.X^2*Polynomial.C (q 1018) := by ring
    _ = _ := by rw [hp]; ring

def rowCode : High ⊕ Unit → Nat
  | .inl i => i.val.val
  | .inr _ => 1022

def columnQ : High ⊕ Unit → Nat → F
  | .inl j => chosenQ (Pi.single j 1)
  | .inr _ => R706ExtraActiveColumn.extraQ

def fullMatrix (half : F) : Matrix (High ⊕ Unit) (High ⊕ Unit) (Polynomial F) :=
  fun i j => polyChord half (columnQ j) (rowCode i)

def extraColumn (half : F) : Matrix High Unit (Polynomial F) :=
  fun i _ => polyChord half R706ExtraActiveColumn.extraQ i.val.val

lemma column_top (j : High ⊕ Unit) : columnQ (F:=F) j 1022=0 ∧ columnQ (F:=F) j 1023=0 := by
  cases j with
  | inl j => exact ⟨(chosenQ_top_zero (Pi.single j 1)).2.2.1,(chosenQ_top_zero (Pi.single j 1)).2.2.2⟩
  | inr j => exact ⟨R706ExtraActiveColumn.extraQ_top.2.2.1,R706ExtraActiveColumn.extraQ_top.2.2.2⟩

lemma full_update (half : F) (h2 : (2:F) ≠ 0) :
    (fullMatrix half).updateRow (.inr ())
      ((fullMatrix half) (.inr ()) +
        (Polynomial.C (half/2)*Polynomial.X) •
          (fullMatrix half) (.inl R706ExtraActiveColumn.precedingHigh)) =
      Matrix.fromBlocks (polyMatrix half) (extraColumn half) 0
        (fun _ _ => Polynomial.C (half/2)*Polynomial.X^2) := by
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [Matrix.updateRow,fullMatrix,rowCode,columnQ,polyChord,polyMatrix,scalarMatrix]
    | inr j => simp [Matrix.updateRow,fullMatrix,rowCode,columnQ,extraColumn]
  | inr i =>
    cases i
    have hrow : ∀ j : High ⊕ Unit,
        (fullMatrix half) (.inr ()) j +
          (Polynomial.C (half/2)*Polynomial.X)*(fullMatrix half) (.inl R706ExtraActiveColumn.precedingHigh) j =
          (Polynomial.C (half/2)*Polynomial.X^2)*Polynomial.C (columnQ j 1018) := by
      intro j
      exact polyChord_top_pivot half (columnQ j) h2 (column_top j).1 (column_top j).2
    cases j with
    | inl j =>
      simpa [Matrix.updateRow,Pi.smul_apply,smul_eq_mul,chosenQ_1018_zero,columnQ] using hrow (.inl j)
    | inr j =>
      cases j
      simpa [Matrix.updateRow,Pi.smul_apply,smul_eq_mul,columnQ,R706ExtraActiveColumn.extraQ_1018] using hrow (.inr ())

theorem full_det_factor (half : F) (h2 : (2:F) ≠ 0) :
    (fullMatrix half).det = (polyMatrix half).det *
      (Polynomial.C (half/2)*Polynomial.X^2) := by
  have hrow : (Sum.inr () : High ⊕ Unit) ≠ Sum.inl R706ExtraActiveColumn.precedingHigh := by simp
  calc
    _ = ((fullMatrix half).updateRow (.inr ())
      ((fullMatrix half) (.inr ()) + (Polynomial.C (half/2)*Polynomial.X) •
        (fullMatrix half) (.inl R706ExtraActiveColumn.precedingHigh))).det :=
      (Matrix.det_updateRow_add_smul_self (fullMatrix half) hrow _).symm
    _ = (Matrix.fromBlocks (polyMatrix half) (extraColumn half) 0
      (fun _ _ => Polynomial.C (half/2)*Polynomial.X^2)).det :=
      congrArg Matrix.det (full_update half h2)
    _ = _ := by rw [Matrix.det_fromBlocks_zero₂₁]; simp

theorem full_det_ne_zero (half : F) (hhalf : half ≠ 0) (h2 : (2:F) ≠ 0) :
    (fullMatrix half).det ≠ 0 := by
  rw [full_det_factor half h2]
  apply mul_ne_zero (polyMatrix_det_ne_zero half h2)
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr (div_ne_zero hhalf h2))
    (pow_ne_zero 2 Polynomial.X_ne_zero)

#print axioms polyChord_eval
#print axioms polyChord_top_pivot
#print axioms full_update
#print axioms full_det_factor
#print axioms full_det_ne_zero
end
end AspisV8R19.R707FullActiveDeterminant
