/- Pure index preflight: at most 513 ten-bit schedules, no field recurrence
   or large determinant reduction. Field weights stay symbolic. -/
import AspisV8R17.WeightedScatter
import AspisV8R19.LowGResidualSupport

namespace AspisR19.SourceEdgeGrowth
open AspisV8R17

def growthBounded (n : Nat) : Bool :=
  (List.range ((n+15)/16)).all fun block =>
    (List.range 16).all fun offset =>
      let j := block*16+offset
      if j<n then (indexTargets j).all fun r => decide (r≤j+1) else true

theorem growth512 : growthBounded 512=true := by decide
theorem growth513 : growthBounded 513=true := by decide

theorem growth_sound (n j : Nat) (h : growthBounded n=true) (hj : j<n) :
    ∀ r ∈ indexTargets j, r≤j+1 := by
  simp only [growthBounded,List.all_eq_true,List.mem_range] at h
  have hb : j/16 < (n+15)/16 := by omega
  have ho : j%16 < 16 := Nat.mod_lt _ (by decide)
  have hs := h (j/16) hb (j%16) ho
  have he : j/16*16+j%16=j := by omega
  simpa only [he,if_pos hj,List.all_eq_true,decide_eq_true_eq] using hs

variable {F : Type*} [CommRing F]
theorem sourceEdges_growth (half : F) (n : Nat) (h : growthBounded n=true) :
    ∀ e ∈ sourceEdges half n, e.2.1≤e.1+1 := by
  intro e he
  obtain ⟨j,hj,he⟩ := List.mem_flatMap.mp he
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
  apply growth_sound n j h (List.mem_range.mp hj) v.1
  rw [← weighted_targets half j]
  exact List.mem_map.mpr ⟨v,hv,rfl⟩

theorem sourceChord_low_g_zero (half : F) (q : Nat → F)
    (hq : ∀ r, 106≤r → q r=0) (a b c : F) (i : Fin 271) :
    sourceChord half q a b c (128+3*i.val)=0 := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  apply LowGResidualSupport.selected_g_zero _ _
    (sourceEdges_growth half 512 growth512) (sourceEdges_growth half 513 growth513)
  intro r hr
  by_cases hn : r<1024 <;> simp [zeroExtend,hn,hq r hr]

#print axioms growth512
#print axioms growth513
#print axioms growth_sound
#print axioms sourceEdges_growth
#print axioms sourceChord_low_g_zero
end AspisR19.SourceEdgeGrowth
