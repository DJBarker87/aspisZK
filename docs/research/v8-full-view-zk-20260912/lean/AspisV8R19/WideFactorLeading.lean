import AspisV8R19.FactorLeading
import AspisV8R19.SourceNaturalShift

/-! Extend the retained symbolic leading/support argument through degree 31.
Only small integer edge schedules are reduced, never field recurrences. -/
namespace AspisR19.WideFactorLeading
open AspisV8R17 SourceEdgeGrowth SourceNaturalShift
noncomputable section
variable {F : Type*} [CommRing F]

def totalExponent : Nat → Nat
  | 0 => 0
  | n+1 => totalExponent n+countOnes 10 n

theorem top_index : ∀ j : Fin 31,
    (((indexLoop 10 j.val 0).getD []).filter fun e => e.1==j.val+1) =
      [(j.val+1,countOnes 10 j.val)] := by decide
theorem growth32 : growthBounded 32=true := by decide
theorem small_schedule : ∀ n : Fin 33, scheduleBounded n.val=true := by decide

theorem sparseX_top (half : F) (n : Nat) (hn : n<31) :
    sparseX half n (n+1)=half^countOnes 10 n := by
  have hw := weightedIndexLoop_powers half 10 n 0
  simp only [pow_zero] at hw
  unfold sparseX sparseVector
  rw [hw]
  have he : ((indexLoop 10 n 0).map (List.map fun e => (e.1,half^e.2))).getD [] =
      ((indexLoop 10 n 0).getD []).map (fun e => (e.1,half^e.2)) := by
    cases indexLoop 10 n 0 <;> rfl
  rw [he,List.map_map]
  change (((indexLoop 10 n 0).getD []).map fun e => if n+1=e.1 then half^e.2 else 0).sum = _
  rw [FactorLeading.select_sum,top_index ⟨n,hn⟩]
  simp

theorem small_growth (half : F) (n : Nat) (hn : n≤32) :
    ∀ e ∈ sourceEdges half n, e.2.1≤e.1+1 := by
  intro e he
  obtain ⟨j,hj,he⟩ := List.mem_flatMap.mp he
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
  apply growth_sound 32 j growth32 (by have := List.mem_range.mp hj; omega) v.1
  rw [← weighted_targets half j]
  exact List.mem_map.mpr ⟨v,hv,rfl⟩

theorem scatter_above (half : F) (n r : Nat) (hn : n≤32) (hr : n<r)
    (q : Nat → F) : scatterValue (sourceEdges half n) q r=0 := by
  unfold scatterValue
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
  have hg := small_growth half n hn e he
  obtain ⟨j,hj,he⟩ := List.mem_flatMap.mp he
  obtain ⟨v,hv,he⟩ := List.mem_map.mp he
  have hjn := List.mem_range.mp hj
  subst e
  dsimp only at hg
  have h : r≠v.1 := by omega
  simp [h]

theorem scatter_top (half : F) (n : Nat) (hn : n<31) (q : Nat → F) :
    scatterValue (sourceEdges half (n+1)) q (n+1) = q n*half^countOnes 10 n := by
  have splitEdges : sourceEdges half (n+1) = sourceEdges half n ++
      (((weightedIndexLoop half 10 n 0 1).getD []).map fun e => (n,e.1,e.2)) := by
    simp [sourceEdges,List.range_succ,List.flatMap_append]
  rw [splitEdges,scatter_append,scatter_above half n (n+1) (by omega) (by omega),
    zero_add,scatter_column]
  change q n*sparseX half n (n+1)=_
  rw [sparseX_top half n hn]

theorem factor_support (half : F) (roots : List F) (hn : roots.length≤31) :
    ∀ r, roots.length<r → FactorLeading.factor half roots r=0 := by
  induction roots with
  | nil => intro r hr; simp [FactorLeading.factor,show r≠0 by omega]
  | cons root roots ih =>
      intro r hr
      have hlen : roots.length≤31 := by simp only [List.length_cons] at hn; omega
      rw [FactorLeading.factor,scatter_above half (roots.length+1) r (by simp_all; omega) (by simpa using hr),
        ih hlen r (by simp_all; omega)]
      simp

theorem factor_leading (half : F) (roots : List F) (hn : roots.length≤31) :
    FactorLeading.factor half roots roots.length=half^totalExponent roots.length := by
  induction roots with
  | nil => simp [FactorLeading.factor,totalExponent]
  | cons root roots ih =>
      have hlt : roots.length<31 := by simpa using hn
      change scatterValue (sourceEdges half (roots.length+1)) (FactorLeading.factor half roots)
        (roots.length+1)-root*FactorLeading.factor half roots (roots.length+1)=_
      rw [scatter_top half roots.length hlt,
        factor_support half roots (by omega) (roots.length+1) (by omega),
        mul_zero,sub_zero,ih (by omega)]
      simp only [List.length_cons,totalExponent,pow_add]

#print axioms top_index
#print axioms growth32
#print axioms small_schedule
#print axioms sparseX_top
#print axioms small_growth
#print axioms scatter_above
#print axioms scatter_top
#print axioms factor_support
#print axioms factor_leading
end
end AspisR19.WideFactorLeading
