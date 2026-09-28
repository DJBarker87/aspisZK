/- Reuse the actual source-shaped scatter/chord model from R17.
   The edge-growth condition and source/layout refinement remain explicit. -/
import AspisV8R17.SourceScatter

namespace AspisR19.LowKernelSeparation
open AspisV8R17
variable {F : Type*} [CommRing F]

theorem scatter_support_step (edges : List (ScatterEdge Nat Nat F))
    (hedges : ∀ e ∈ edges, e.2.1 ≤ e.1+1)
    (q : Nat → F) (n : Nat) (hq : ∀ i, n≤i → q i=0)
    (r : Nat) (hr : n+1≤r) : scatterValue edges q r=0 := by
  induction edges with
  | nil => simp [scatterValue]
  | cons e es ih =>
    have he := hedges e (by simp)
    have hs : ∀ e ∈ es, e.2.1≤e.1+1 := by
      intro e h; exact hedges e (by simp [h])
    have hz : (if r=e.2.1 then e.2.2*q e.1 else 0)=0 := by
      by_cases h : r=e.2.1
      · rw [if_pos h,hq e.1 (by omega),mul_zero]
      · rw [if_neg h]
    simpa only [scatterValue,List.map_cons,List.sum_cons,hz,zero_add] using ih hs

theorem low_even (x xx : List (ScatterEdge Nat Nat F))
    (hx : ∀ e ∈ x, e.2.1≤e.1+1) (hxx : ∀ e ∈ xx, e.2.1≤e.1+1)
    (q : Nat → F) (hq : ∀ i, 88≤i → q i=0)
    (a b c : F) (r : Nat) (hr : 46≤r) : chordEven x xx q a b c r=0 := by
  have he : ∀ i, 44≤i → q (2*i)=0 := by intro i hi; exact hq _ (by omega)
  have ho : ∀ i, 44≤i → q (2*i+1)=0 := by intro i hi; exact hq _ (by omega)
  have xe := scatter_support_step x hx (fun i => q (2*i)) 44 he r (by omega)
  have xo : ∀ i, 45≤i → scatterValue x (fun j => q (2*j+1)) i=0 := by
    intro i hi; exact scatter_support_step x hx _ 44 ho i hi
  have xxo := scatter_support_step xx hxx _ 45 xo r hr
  simp only [chordEven,hq (2*r) (by omega),hq (2*r+1) (by omega),xe,xxo,
    mul_zero,sub_self,add_zero]

theorem low_odd (x : List (ScatterEdge Nat Nat F))
    (hx : ∀ e ∈ x, e.2.1≤e.1+1)
    (q : Nat → F) (hq : ∀ i, 88≤i → q i=0)
    (a b c : F) (r : Nat) (hr : 45≤r) : chordOdd x q a b c r=0 := by
  have ho : ∀ i, 44≤i → q (2*i+1)=0 := by intro i hi; exact hq _ (by omega)
  have xo := scatter_support_step x hx _ 44 ho r hr
  simp only [chordOdd,hq (2*r) (by omega),hq (2*r+1) (by omega),xo,mul_zero,add_zero]

theorem low_chord (x xx : List (ScatterEdge Nat Nat F))
    (hx : ∀ e ∈ x, e.2.1≤e.1+1) (hxx : ∀ e ∈ xx, e.2.1≤e.1+1)
    (q : Nat → F) (hq : ∀ i, 88≤i → q i=0)
    (a b c : F) (r : Nat) (hr : 91≤r) : chordCoefficient x xx q a b c r=0 := by
  unfold chordCoefficient
  split
  · rename_i h
    exact low_even x xx hx hxx q hq a b c (r/2) (by omega)
  · exact low_odd x hx q hq a b c (r/2) (by omega)

theorem high_observation_retained (x xx : List (ScatterEdge Nat Nat F))
    (hx : ∀ e ∈ x, e.2.1≤e.1+1) (hxx : ∀ e ∈ xx, e.2.1≤e.1+1)
    (q s : Nat → F) (sameHigh : ∀ i, 88≤i → q i=s i)
    (a b c : F) (r : Nat) (hr : 91≤r) :
    chordCoefficient x xx q a b c r=chordCoefficient x xx s a b c r := by
  have hd : ∀ i, 88≤i → (1:F)*q i+(-1)*s i=0 := by
    intro i hi; rw [sameHigh i hi]; ring
  have h := low_chord x xx hx hxx _ hd a b c r hr
  rw [chordCoefficient_linear] at h
  exact sub_eq_zero.mp (by simpa only [one_mul,neg_one_mul,← sub_eq_add_neg] using h)

#print axioms scatter_support_step
#print axioms low_even
#print axioms low_odd
#print axioms low_chord
#print axioms high_observation_retained
end AspisR19.LowKernelSeparation
