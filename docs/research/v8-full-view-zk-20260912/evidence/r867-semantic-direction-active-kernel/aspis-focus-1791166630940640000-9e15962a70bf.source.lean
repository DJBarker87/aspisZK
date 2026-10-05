import AspisV8R19.R787PairSupportZero
import AspisV8R19.R743JointSparseEntryBinding

set_option autoImplicit false
namespace AspisV8R19.R867SemanticDirectionActiveKernel
open AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R773LowActiveKernel
open AspisV8R19.R698ActiveCoreLayout
open AspisV8R19.R707FullActiveDeterminant
noncomputable section
variable {F : Type*} [CommRing F]

theorem inactive_five : ∀ n : Fin 5,
    (⟨384+n.val, by omega⟩ : Fin 1024) ∉ activeCode := by decide

theorem active_outside_five (j : J) :
    ¬ (384 ≤ rowCode j ∧ rowCode j ≤ 388) := by
  rcases j with i | u
  · have hm : i.val ∈ activeCode := (Finset.mem_filter.mp i.property).1
    intro hb
    change 384 ≤ i.val.val ∧ i.val.val ≤ 388 at hb
    let n : Fin 5 := ⟨i.val.val-384, by omega⟩
    have he : (⟨384+n.val, by omega⟩ : Fin 1024) = i.val := by
      apply Fin.ext
      dsimp [n]
      omega
    exact inactive_five n (he.symm ▸ hm)
  · simp [rowCode]

theorem pairSupport_96_0_absent (r : Nat)
    (hout : ¬ (384 ≤ r ∧ r ≤ 388)) :
    ¬ pairSupport (96 : Fin 255) (0 : Fin 3) r := by
  have h192 : indexTargets 192 = [193] := by rfl
  have h193 : indexTargets 193 = [192,194] := by rfl
  simp only [pairSupport, Fin.val_zero, Fin.val_ofNat, if_false, if_true,
    Nat.mul_zero, Nat.add_zero, Nat.zero_div, evenUnitSupport, oddUnitSupport]
  rw [h192, h193]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem all_active_zero (half alpha a b c : F) (j : J) :
    sourceChord half (direction alpha (96 : Fin 255) (0 : Fin 3)) a b c
      (rowCode j) = 0 := by
  exact direction_sourceChord_zero_of_not_pairSupport half alpha a b c 96 0
    (rowCode j) (rowCode_ge_96 j) (pairSupport_96_0_absent _ (active_outside_five j))

theorem raw_active_zero (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (j : J) :
    rawObservation half quarter a b c kappa tau z
      (indexedDirection alpha (96 : Fin 255) (0 : Fin 3)) (.inl j) = 0 := by
  rw [rawObservation_indexedDirection]
  exact all_active_zero half alpha a b c j

#print axioms inactive_five
#print axioms active_outside_five
#print axioms pairSupport_96_0_absent
#print axioms all_active_zero
#print axioms raw_active_zero
end
end AspisV8R19.R867SemanticDirectionActiveKernel
