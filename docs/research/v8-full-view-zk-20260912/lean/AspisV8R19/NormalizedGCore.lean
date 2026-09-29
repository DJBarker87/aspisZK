import AspisV8R19.NormalizedQuotient
import AspisV8R19.HighQueryGCore
import AspisV8R19.SparseHighWitness

/-! Four-slot coefficients are flattened in their source order, then fed to
the retained finite source-shaped chord. This proves preservation of all
271 sparse G reads, not an extracted-Rust or full-view theorem. -/
namespace AspisR19.NormalizedGCore
open AspisV8R17 HighRepairInvariant HighQueryGCore SparseHighWitness
noncomputable section
variable {F : Type*} [CommRing F]

def flatten (q : Index 32 → F) (r : Nat) : F :=
  if h : r<128 then q (⟨r/4,by omega⟩,⟨r%4,by omega⟩) else 0

theorem flatten_column (alpha : F) (d : Fin 32) (s : Fin 4) :
    flatten (column alpha d s) =
      fun r => unitVector (4*d.val+s.val) r-alpha^s.val*unitVector (4*d.val) r := by
  funext r
  by_cases hr : r<128
  · have he (k : Fin 4) :
        ((⟨r/4,by omega⟩,⟨r%4,by omega⟩) : Index 32)=(d,k) ↔ r=4*d.val+k.val := by
      simp only [Prod.mk.injEq,Fin.ext_iff]
      have hk := k.isLt
      omega
    simp only [flatten,dif_pos hr,column,unit,he,unitVector,Fin.val_zero,add_zero]
  · have hd := d.isLt
    have hs := s.isLt
    have h1 : r ≠ 4*d.val+s.val := by omega
    have h0 : r ≠ 4*d.val := by omega
    simp [flatten,hr,unitVector,h1,h0]

theorem flatten_high (q v : Index 32 → F)
    (same : ∀ i, 22 ≤ i.1.val → q i=v i) (r : Nat) (hr : 88 ≤ r) :
    flatten q r=flatten v r := by
  unfold flatten
  split
  · exact same _ (by change 22 ≤ r/4; omega)
  · rfl

theorem selected_direct_g_zero (half alpha a b c : F) (j : Fin 13) (i : Fin 271) :
    sourceChord half (flatten (column alpha (degree j) (slot j))) a b c (128+3*i.val)=0 := by
  rw [flatten_column]
  by_cases hj : j.val<12
  · rw [sourceChord_difference]
    have hd : (degree j).val<28 := by simp only [degree,if_pos hj]; omega
    have hs := (slot j).isLt
    rw [unit_g_zero half a b c _ (by omega),unit_g_zero half a b c _ (by omega)]
    simp
  · simp only [degree,slot,if_neg hj]
    exact exceptional_g_zero half alpha a b c i

section Field
variable {K : Type*} [Field K] [NeZero (2 : K)]

theorem normalized_selected_g_zero (t : Fin 22 → K) (ht : Function.Injective t)
    (half alpha a b c : K) (j : Fin 13) (i : Fin 271) :
    sourceChord half (flatten (NormalizedQuotient.quotient t ht alpha (degree j) (slot j)))
      a b c (128+3*i.val)=0 := by
  rw [low_repair_preserves_g half _ (flatten (column alpha (degree j) (slot j)))
    (flatten_high _ _ (fun r hr => NormalizedQuotient.quotient_high t ht _ _ _ r hr))]
  exact selected_direct_g_zero half alpha a b c j i
end Field

#print axioms flatten_column
#print axioms flatten_high
#print axioms selected_direct_g_zero
#print axioms normalized_selected_g_zero
end
end AspisR19.NormalizedGCore
