import AspisV8R17.SourceOriginalWeights
import AspisV8R19.SourceCircleBoundary

/-! Exact source-shaped tensor/transport pairing. The full low chord output
has 131 coordinates; the old 111-coordinate residual cutoff is not reused. -/
namespace AspisR19.FullPointFunctional
open AspisV8R16 AspisV8R17 HighRepairInvariant NormalizedGCore SourceMaskTransport
open T163SourceTable
noncomputable section
variable {F : Type*} [CommRing F]

theorem source_tensor (z : Fin 10 → F) (r : Nat) :
    sourcePointBasis z r=ResidualModel.tensor z r := by
  simp only [sourcePointBasis,sourceMultilinearFactors,List.prod_ofFn,
    ResidualModel.tensor,Nat.shiftRight_eq_div_pow,Nat.and_one_is_mod]

def lowIndex (j : Fin 131) : Fin 1024 := ⟨j.val,by omega⟩

theorem low_not_pivot (j : Fin 131) : order (lowIndex j)≠1023 := by
  intro h
  have he := order.injective (h.trans pivot_fixed.symm)
  have hv := congrArg Fin.val he
  have hj := j.isLt
  simp only [lowIndex,Fin.val_ofNat] at hv
  omega

def codeWeight (w : Fin 1024 → F) (j : Fin 131) : F :=
  w (order (lowIndex j))-(if isInactive (order (lowIndex j)) then w 1023 else 0)

theorem codeWeight_eq (w : Fin 1024 → F) (j : Fin 131) :
    codeWeight w j=transportDual inactive 1023 order w (lowIndex j) := by
  have hp := low_not_pivot j
  simp only [codeWeight,transportDual,Finset.mem_erase,hp,not_false_eq_true,
    true_and,inactive,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp_all

theorem low_dot_restrict (w c : Fin 1024 → F)
    (tail : ∀ j, 131≤j.val → c j=0) :
    (∑ j : Fin 1024,w j*c j)=∑ j : Fin 131,w (lowIndex j)*c (lowIndex j) := by
  rw [Fin.sum_univ_add (a:=131) (b:=893)]
  have htail : (∑ j : Fin 893,w (Fin.natAdd 131 j)*c (Fin.natAdd 131 j))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [tail _ (by simp [Fin.natAdd]),mul_zero]
  rw [htail,add_zero]
  rfl

theorem mask_pairing (half a b c : F) (q : Index 32 → F) (w : Fin 1024 → F) :
    (∑ r : Fin 1024,w r*mask half a b c q r)=
      ∑ j : Fin 131,codeWeight w j*sourceChord half (flatten q) a b c j.val := by
  rw [mask,inverseTransport_dot,low_dot_restrict _ _ (code_tail half a b c q)]
  apply Finset.sum_congr rfl
  intro j _
  rw [codeWeight_eq]
  rfl

def tensorCode (z : Fin 10 → F) (j : Fin 131) : F :=
  ResidualModel.tensor z (order (lowIndex j)).val-
    (if isInactive (order (lowIndex j)) then ResidualModel.tensor z 1023 else 0)

theorem point_pairing (half a b c : F) (q : Index 32 → F) (z : Fin 10 → F) :
    sourcePointFunctional z (mask half a b c q)=
      ∑ j : Fin 131,tensorCode z j*sourceChord half (flatten q) a b c j.val := by
  rw [sourcePointFunctional,mask_pairing]
  simp only [codeWeight,tensorCode,source_tensor]
  rfl

#print axioms source_tensor
#print axioms low_not_pivot
#print axioms codeWeight_eq
#print axioms low_dot_restrict
#print axioms mask_pairing
#print axioms point_pairing
end
end AspisR19.FullPointFunctional
