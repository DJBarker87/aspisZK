/- Source-shaped carry recurrence for degrees needed by the low residual.
   Only the 26 small integer schedules are reduced; field values stay symbolic. -/
import AspisV8R19.SourceEdgeGrowth
import AspisV8R19.LowResidualFactor
import Mathlib.LinearAlgebra.Matrix.Block

namespace AspisR19.FactorLeading
open AspisV8R17 AspisR19.SourceEdgeGrowth
variable {F : Type*} [CommRing F]
noncomputable section

def edgeExponent (j : Nat) : Nat :=
  [0,1,0,2,0,1,0,3,0,1,0,2,0,1,0,4,0,1,0,2,0,1,0,3,0,1].getD j 0

def totalExponent : Nat → Nat
  | 0 => 0
  | n+1 => totalExponent n+edgeExponent n

theorem top_index : ∀ j : Fin 26,
    (((indexLoop 10 j.val 0).getD []).filter fun e => e.1==j.val+1) =
      [(j.val+1,edgeExponent j.val)] := by decide

theorem growth27 : growthBounded 27=true := by decide

theorem select_sum (xs : List (Nat × Nat)) (half : F) (r : Nat) :
    (xs.map fun e => if r=e.1 then half^e.2 else 0).sum =
      ((xs.filter fun e => e.1==r).map fun e => half^e.2).sum := by
  induction xs with
  | nil => simp
  | cons e es ih =>
      by_cases h : r=e.1
      · subst r; simp [ih]
      · have hn : e.1≠r := Ne.symm h
        simp [h,hn,ih]

theorem sparseX_top (half : F) (n : Nat) (hn : n<26) :
    sparseX half n (n+1)=half^edgeExponent n := by
  have hw := weightedIndexLoop_powers half 10 n 0
  simp only [pow_zero] at hw
  unfold sparseX sparseVector
  rw [hw]
  have he : ((indexLoop 10 n 0).map (List.map fun e => (e.1,half^e.2))).getD [] =
      ((indexLoop 10 n 0).getD []).map (fun e => (e.1,half^e.2)) := by
    cases indexLoop 10 n 0 <;> rfl
  rw [he,List.map_map]
  change (((indexLoop 10 n 0).getD []).map fun e => if n+1=e.1 then half^e.2 else 0).sum = _
  rw [select_sum,top_index ⟨n,hn⟩]
  simp

theorem small_growth (half : F) (n : Nat) (hn : n≤27) :
    ∀ e ∈ sourceEdges half n, e.2.1≤e.1+1 := by
  intro e he
  obtain ⟨j,hj,he⟩ := List.mem_flatMap.mp he
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
  apply growth_sound 27 j growth27 (by have := List.mem_range.mp hj; omega) v.1
  rw [← weighted_targets half j]
  exact List.mem_map.mpr ⟨v,hv,rfl⟩

theorem scatter_above (half : F) (n r : Nat) (hn : n≤27) (hr : n<r)
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

theorem scatter_top (half : F) (n : Nat) (hn : n<26) (q : Nat → F) :
    scatterValue (sourceEdges half (n+1)) q (n+1) = q n*half^edgeExponent n := by
  have splitEdges : sourceEdges half (n+1) = sourceEdges half n ++
      (((weightedIndexLoop half 10 n 0 1).getD []).map fun e => (n,e.1,e.2)) := by
    simp [sourceEdges,List.range_succ,List.flatMap_append]
  rw [splitEdges,scatter_append,scatter_above half n (n+1) (by omega) (by omega),
    zero_add,scatter_column]
  change q n*sparseX half n (n+1)=_
  rw [sparseX_top half n hn]

def factor (half : F) : List F → Nat → F
  | [],r => if r=0 then 1 else 0
  | root::roots,r => scatterValue (sourceEdges half (roots.length+1))
      (factor half roots) r-root*factor half roots r

theorem factor_support (half : F) (roots : List F) (hn : roots.length≤26) :
    ∀ r, roots.length<r → factor half roots r=0 := by
  induction roots with
  | nil => intro r hr; simp [factor,show r≠0 by omega]
  | cons root roots ih =>
      intro r hr
      have hlen : roots.length≤26 := by simp only [List.length_cons] at hn; omega
      rw [factor,scatter_above half (roots.length+1) r (by simp_all; omega) (by simpa using hr),
        ih hlen r (by simp_all; omega)]
      simp

theorem factor_leading (half : F) (roots : List F) (hn : roots.length≤26) :
    factor half roots roots.length=half^totalExponent roots.length := by
  induction roots with
  | nil => simp [factor,totalExponent]
  | cons root roots ih =>
      have hlt : roots.length<26 := by simpa using hn
      change scatterValue (sourceEdges half (roots.length+1)) (factor half roots)
        (roots.length+1)-root*factor half roots (roots.length+1)=_
      rw [scatter_top half roots.length hlt,
        factor_support half roots (by omega) (roots.length+1) (by omega),
        mul_zero,sub_zero,ih (by omega)]
      simp only [List.length_cons,totalExponent,pow_add]

def changeMatrix (half : F) (roots : List F) : Matrix (Fin 13) (Fin 13) F :=
  fun i j => if i.val%3=j.val%3 then
    factor half (List.replicate (j.val/3) 0 ++ roots) (22+i.val/3) else 0

theorem change_upper (half : F) (roots : List F) (hl : roots.length=22) :
    (changeMatrix half roots).BlockTriangular id := by
  intro i j hij
  unfold changeMatrix
  split_ifs with h
  · have hi := i.isLt
    have hj := j.isLt
    have hv : j.val < i.val := hij
    apply factor_support half _ (by simp [hl]; omega)
    simp [hl]
    omega
  · rfl

theorem change_diagonal (half : F) (roots : List F) (hl : roots.length=22)
    (i : Fin 13) : changeMatrix half roots i i=half^totalExponent (22+i.val/3) := by
  have he : (List.replicate (i.val/3) (0:F) ++ roots).length=22+i.val/3 := by simp [hl,Nat.add_comm]
  unfold changeMatrix
  rw [if_pos rfl]
  rw [← he,factor_leading half _ (by rw [he]; have := i.isLt; omega)]

theorem change_determinant (half : F) (roots : List F) (hl : roots.length=22) :
    (changeMatrix half roots).det=half^269 := by
  rw [Matrix.det_of_upperTriangular (change_upper half roots hl)]
  simp only [change_diagonal half roots hl]
  simp [Fin.prod_univ_succ,totalExponent,edgeExponent]
  ring

theorem factor_minor_nonzero {K : Type*} [Field K] (half : K) (hh : half≠0)
    (roots : List K) (hl : roots.length=22) (D : Matrix (Fin 13) (Fin 13) K) :
    (D*changeMatrix half roots).det≠0 ↔ D.det≠0 :=
  LowResidualFactor.basis_change_nonzero D _ half hh (change_determinant half roots hl)

#print axioms top_index
#print axioms growth27
#print axioms select_sum
#print axioms sparseX_top
#print axioms small_growth
#print axioms scatter_above
#print axioms scatter_top
#print axioms factor_support
#print axioms factor_leading
#print axioms change_upper
#print axioms change_diagonal
#print axioms change_determinant
#print axioms factor_minor_nonzero
end
end AspisR19.FactorLeading
