import AspisV8R19.TwoSwapSourceTable
import AspisV8R19.FullResidualBoundary
import AspisV8R19.AugmentedMaskTransport

/-! Arbitrary-field/challenge low restriction for the actual two-swap map.
The image updates are retained in the source expression and vanish only
after the quotient-coordinate support restriction. No numeric specialization
or rank premise is used here. This remains exact-field, not Rust word code. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapSourceWeights
open AspisV8R16 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open TwoSwapSourceTable NormalizedGCore
noncomputable section
variable {F : Type*} [CommRing F]

def codeWeight (w : Fin 1024 → F) (j : Fin 131) : F :=
  w (order (lowIndex j))-(if isInactive (order (lowIndex j)) then w 1023 else 0)

theorem codeWeight_eq (w : Fin 1024 → F) (j : Fin 131) :
    codeWeight w j=transportDual inactive 1023 order w (lowIndex j) := by
  have hp:=low_not_pivot j
  simp only [codeWeight,transportDual,Finset.mem_erase,
    T163SourceTable.inactive,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp_all

def pointWeight (half a b c : F) (w : Fin 1024 → F) (r : Fin 128) : F :=
  ∑ j : Fin 131,codeWeight w j*ResidualModel.chordEntry half a b c r.val j.val

theorem transpose_low (half a b c : F) (w : Nat → F) (r : Fin 128) :
    sourceChordTranspose half w a b c r.val=
      ∑ j : Fin 131,w j.val*ResidualModel.chordEntry half a b c r.val j.val := by
  have h:=source_chord_transpose_pairing half (unitVector r.val) w a b c
  have hr : r.val<1024 := by omega
  have right : rangeDot 1024 (sourceChordTranspose half w a b c) (unitVector r.val)=
      sourceChordTranspose half w a b c r.val := by
    simp [rangeDot,unitVector,hr]
  rw [right] at h
  have left : rangeDot 1024 w (sourceChord half (unitVector r.val) a b c)=
      ∑ j : Fin 131,w j.val*ResidualModel.chordEntry half a b c r.val j.val := by
    unfold rangeDot
    rw [← Fin.sum_univ_eq_sum_range]
    rw [FullPointFunctional.low_dot_restrict _ _ (FullQuotientWeights.unit_tail half a b c r)]
    apply Finset.sum_congr rfl
    intro j _
    rw [ResidualModel.chordEntry_eq half a b c r.val j.val hr]
    rfl
  exact h.symm.trans left

theorem transpose_entry (half a b c : F) (w : Fin 1024 → F) (r : Fin 128) :
    sourceChordTranspose half (extendFin1024 (transportDual inactive 1023 order w))
      a b c r.val=pointWeight half a b c w r := by
  rw [transpose_low]
  unfold pointWeight
  apply Finset.sum_congr rfl
  intro j _
  rw [codeWeight_eq]
  simp only [extendFin1024,dif_pos (show j.val<1024 by omega)]
  rfl

theorem quotient_entry (half a b c tau : F) (structured : Bool)
    (w : Fin 1024 → F) (r : Fin 128) :
    sourceQuotientWeights half (extendFin1024 (transportDual inactive 1023 order w))
      a b c tau structured r.val=pointWeight half a b c w r := by
  rw [sourceQuotientWeights,sourceImageUpdates_apply,transpose_entry]
  simp [show r.val≠1023 by omega,show r.val≠1022 by omega,show r.val≠1021 by omega]

def blockWeight (half a b c : F) (w : Fin 1024 → F) (i : Index 32) : F :=
  pointWeight half a b c w ⟨4*i.1.val+i.2.val,by omega⟩

theorem source_coefficient (half a b c tau quarter : F) (structured : Bool)
    (w : Fin 1024 → F) (q : Index 32 → F) (k : Nat) :
    coefficient (sourceKernel 256 k quarter)
      (fun i => flatten q (4*i.1.val+i.2.val))
      (fun i => sourceQuotientWeights half (extendFin1024 (transportDual inactive 1023 order w))
        a b c tau structured (4*i.1.val+i.2.val))=
      coefficient (sourceKernel 32 k quarter) q (blockWeight half a b c w) := by
  rw [FullCoefficientBoundary.coefficient_blocks,FullCoefficientBoundary.coefficient_blocks,
    Fin.sum_univ_add (a:=32) (b:=224)]
  have hz : (∑ d : Fin 224, ∑ s : Fin 4, ∑ t : Fin 4,
      (if s.val+(4-t.val)%4=k then quarter else 0)*
        flatten q (4*(Fin.natAdd 32 d).val+s.val)*
        sourceQuotientWeights half (extendFin1024 (transportDual inactive 1023 order w))
          a b c tau structured (4*(Fin.natAdd 32 d).val+t.val))=0 := by
    apply Finset.sum_eq_zero
    intro d _
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro t _
    simp [flatten,Fin.natAdd,show ¬4*(32+d.val)+s.val<128 by omega]
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.val_castAdd,FullCoefficientBoundary.low_slot]
  rw [quotient_entry half a b c tau structured w ⟨4*d.val+t.val,by omega⟩]
  rfl

def mask (half a b c : F) (q : Index 32 → F) : Fin 1024 → F :=
  inverseTransport inactive 1023 order (fun j => sourceChord half (flatten q) a b c j.val)

/- The older generic flattening lemma unnecessarily required a field. Keep
this ring-level version so polynomial instantiation needs no fake inverses. -/
private theorem sum_quads (n : Nat) (f : Nat → F) :
    (∑ r ∈ Finset.range (4*n),f r)=
      ∑ i ∈ Finset.range n,(f (4*i)+f (4*i+1)+f (4*i+2)+f (4*i+3)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 4*(n+1)=4*n+1+1+1+1 by omega]
    rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,
      Finset.sum_range_succ,ih,Finset.sum_range_succ]
    ring

theorem flattened_pairing (q : Index 32 → F) (w : Nat → F) :
    rangeDot 1024 w (flatten q)=∑ i : Index 32,q i*w (4*i.1.val+i.2.val) := by
  unfold rangeDot
  rw [show (1024:Nat)=128+896 by decide,Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range 896,w (128+i)*flatten q (128+i))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [flatten,show ¬128+i<128 by omega]
  rw [hz,add_zero]
  change (∑ i ∈ Finset.range (4*32),w i*flatten q i)=_
  rw [sum_quads,Finset.sum_range,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  have h0:=FullCoefficientBoundary.low_slot q d (0:Fin 4)
  have h1:=FullCoefficientBoundary.low_slot q d (1:Fin 4)
  have h2:=FullCoefficientBoundary.low_slot q d (2:Fin 4)
  have h3:=FullCoefficientBoundary.low_slot q d (3:Fin 4)
  simp at h0 h1 h2 h3
  simp [Fin.sum_univ_succ,h0,h1,h2,h3]
  ring

theorem mask_pairing (half a b c : F) (q : Index 32 → F) (w : Fin 1024 → F) :
    (∑ r : Fin 1024,w r*mask half a b c q r)=
      ∑ i : Index 32,q i*blockWeight half a b c w i := by
  have h:=transported_source_opening_pairing half inactive 1023 order w (flatten q) a b c (0:F) false
  simp only [Bool.false_eq_true,if_false,zero_mul,zero_pow (by decide : (2:Nat)≠0),add_zero] at h
  change rangeDot 1024 (sourceQuotientWeights half
    (extendFin1024 (transportDual inactive 1023 order w)) a b c 0 false)
    (flatten q)=(∑ r : Fin 1024,w r*mask half a b c q r) at h
  rw [← h,flattened_pairing]
  apply Finset.sum_congr rfl
  intro i _
  rw [quotient_entry half a b c 0 false w ⟨4*i.1.val+i.2.val,by omega⟩]
  rfl

theorem source_point (half a b c : F) (q : Index 32 → F) (z : Fin 10 → F) :
    sourcePointFunctional z (mask half a b c q)=
      ∑ i : Index 32,q i*blockWeight half a b c (fun r => sourcePointBasis z r.val) i :=
  mask_pairing half a b c q (fun r => sourcePointBasis z r.val)

#print axioms codeWeight_eq
#print axioms transpose_low
#print axioms transpose_entry
#print axioms quotient_entry
#print axioms source_coefficient
#print axioms flattened_pairing
#print axioms mask_pairing
#print axioms source_point
end
end AspisR19.TwoSwapSourceWeights
