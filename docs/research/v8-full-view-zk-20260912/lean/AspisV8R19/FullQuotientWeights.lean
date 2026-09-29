import AspisV8R19.FullPointFunctional

/-! The complete transported source weight on quotient coordinates below 128.
All 131 potentially nonzero chord outputs are retained. Image updates vanish
here because of the coordinate bound, not because they are removed. -/
namespace AspisR19.FullQuotientWeights
open AspisV8R16 AspisV8R17 FullPointFunctional T163SourceTable
noncomputable section
variable {F : Type*} [CommRing F]

def pointWeight (half a b c : F) (w : Fin 1024 → F) (r : Fin 128) : F :=
  ∑ j : Fin 131,codeWeight w j*ResidualModel.chordEntry half a b c r.val j.val

theorem unit_tail (half a b c : F) (r : Fin 128) (j : Fin 1024)
    (hj : 131≤j.val) : sourceChord half (unitVector r.val) a b c j.val=0 := by
  apply HighQueryGCore.sourceChord_support half _ 64 _ a b c _ hj
  intro i hi
  simp [unitVector,show i≠r.val by omega]

theorem transpose_entry (half a b c : F) (w : Fin 1024 → F) (r : Fin 128) :
    sourceChordTranspose half (extendFin1024 (transportDual inactive 1023 order w))
      a b c r.val=pointWeight half a b c w r := by
  have h := source_chord_transpose_pairing half (unitVector r.val)
    (extendFin1024 (transportDual inactive 1023 order w)) a b c
  rw [rangeDot_extendFin1024,low_dot_restrict _ _ (unit_tail half a b c r)] at h
  have hr : r.val<1024 := by omega
  simp only [rangeDot,unitVector,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_range,hr,if_true] at h
  rw [← h]
  unfold pointWeight
  apply Finset.sum_congr rfl
  intro j _
  rw [codeWeight_eq,ResidualModel.chordEntry_eq half a b c r.val j.val hr]
  rfl

theorem quotient_entry (half a b c tau : F) (structured : Bool)
    (w : Fin 1024 → F) (r : Fin 128) :
    sourceQuotientWeights half (extendFin1024 (transportDual inactive 1023 order w))
      a b c tau structured r.val=pointWeight half a b c w r := by
  rw [sourceQuotientWeights,sourceImageUpdates_apply,transpose_entry]
  simp [show r.val≠1023 by omega,show r.val≠1022 by omega,show r.val≠1021 by omega]

#print axioms unit_tail
#print axioms transpose_entry
#print axioms quotient_entry
end
end AspisR19.FullQuotientWeights
