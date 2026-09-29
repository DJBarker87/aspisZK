import AspisV8R19.WideFactorLeading

namespace AspisR19.SourceFactorEvaluation
open AspisV8R17 AspisCircleTensorBinding SourceNaturalShift WideFactorLeading
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def line (n : Nat) (v : Nat → F) (x : F) : F :=
  ∑ i ∈ Finset.range n, naturalLineValue x i*v i

theorem line_sub (n : Nat) (u v : Nat → F) (s x : F) :
    line n (fun i => u i-s*v i) x=line n u x-s*line n v x := by
  simp only [line,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem line_restrict (m n : Nat) (hmn : m≤n) (v : Nat → F)
    (tail : ∀ i, m ≤ i → i < n → v i=0) (x : F) : line m v x=line n v x := by
  unfold line
  apply Finset.sum_subset (Finset.range_mono hmn)
  intro i hi hnot
  rw [tail i (by simpa only [Finset.mem_range,not_lt] using hnot) (Finset.mem_range.mp hi),mul_zero]

theorem scatter_evaluates (n : Nat) (hn : n≤32) (v : Nat → F) (x : F) :
    line (n+1) (scatterValue (sourceEdges (2:F)⁻¹ n) v) x=x*line n v x := by
  unfold line
  rw [source_scatter_gather_dot _ n (small_schedule ⟨n,by omega⟩),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sourceGather_natural x i (by have := Finset.mem_range.mp hi; omega)]
  ring

theorem factor_evaluates (roots : List F) (hn : roots.length≤31) (x : F) :
    line (roots.length+1) (FactorLeading.factor (2:F)⁻¹ roots) x=
      (roots.map fun t => x-t).prod := by
  induction roots with
  | nil => simp [line,FactorLeading.factor,naturalLineValue]
  | cons root roots ih =>
    have hlen : roots.length≤31 := by simp only [List.length_cons] at hn; omega
    change line (roots.length+1+1)
      (fun i => scatterValue (sourceEdges (2:F)⁻¹ (roots.length+1))
        (FactorLeading.factor (2:F)⁻¹ roots) i-root*FactorLeading.factor (2:F)⁻¹ roots i) x=_
    rw [line_sub,scatter_evaluates _ (by simp only [List.length_cons] at hn; omega)]
    rw [← line_restrict (roots.length+1) (roots.length+1+1) (by omega) _
      (fun i hi _ => factor_support _ roots hlen i (by omega))]
    rw [ih hlen]
    simp only [List.map_cons,List.prod_cons]
    ring

theorem factor_root (roots : List F) (hn : roots.length≤31) (x : F) (hx : x∈roots) :
    line 32 (FactorLeading.factor (2:F)⁻¹ roots) x=0 := by
  rw [← line_restrict (roots.length+1) 32 (by omega) _
    (fun i hi _ => factor_support _ roots hn i (by omega)),factor_evaluates roots hn]
  apply List.prod_eq_zero_iff.mpr
  exact List.mem_map.mpr ⟨x,hx,sub_self x⟩

def buildStep (half : F) (state : Nat × (Nat → F)) (root : F) : Nat × (Nat → F) :=
  (state.1+1,fun i => scatterValue (sourceEdges half (state.1+1)) state.2 i-root*state.2 i)

theorem build_factor (half : F) (xs roots : List F) :
    xs.foldl (buildStep half) (roots.length,FactorLeading.factor half roots)=
      ((xs.reverse++roots).length,FactorLeading.factor half (xs.reverse++roots)) := by
  induction xs generalizing roots with
  | nil => simp
  | cons root xs ih =>
    change xs.foldl (buildStep half) ((root::roots).length,FactorLeading.factor half (root::roots))=_
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

def shift (roots : List F) (k : Nat) : Nat → F :=
  FactorLeading.factor (2:F)⁻¹ (List.replicate k 0++roots.reverse)

theorem shift_support (roots : List F) (hl : roots.length=22) (k : Nat) (hk : k<10)
    (i : Nat) (hi : 22+k < i) : shift roots k i=0 := by
  apply factor_support _ _ (by simp [hl]; omega)
  simpa [hl,Nat.add_comm] using hi

theorem shift_pivot_ne_zero (roots : List F) (hl : roots.length=22) (k : Nat) (hk : k<10) :
    shift roots k (22+k)≠0 := by
  have he : (List.replicate k (0:F)++roots.reverse).length=22+k := by simp [hl,Nat.add_comm]
  unfold shift
  rw [← he,factor_leading _ _ (by rw [he]; omega)]
  exact pow_ne_zero _ (inv_ne_zero (NeZero.ne 2))

theorem shift_root (roots : List F) (hl : roots.length=22) (k : Nat) (hk : k<10)
    (x : F) (hx : x∈roots) : line 32 (shift roots k) x=0 := by
  apply factor_root _ (by simp [hl]; omega)
  simp only [List.mem_append,List.mem_reverse]
  exact Or.inr hx

#print axioms line_sub
#print axioms line_restrict
#print axioms scatter_evaluates
#print axioms factor_evaluates
#print axioms factor_root
#print axioms build_factor
#print axioms shift_support
#print axioms shift_pivot_ne_zero
#print axioms shift_root
end
end AspisR19.SourceFactorEvaluation
