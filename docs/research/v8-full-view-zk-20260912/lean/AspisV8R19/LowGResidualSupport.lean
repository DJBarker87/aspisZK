/- The first 13 free kernel columns have quotient support below 106.
   This generic support theorem retains the explicit edge-growth premise. -/
import AspisV8R19.LowKernelSeparation

namespace AspisR19.LowGResidualSupport
open AspisV8R17 AspisR19.LowKernelSeparation
variable {F : Type*} [CommRing F]

theorem low_even (x xx : List (ScatterEdge Nat Nat F))
    (hx : ∀ e ∈ x, e.2.1≤e.1+1) (hxx : ∀ e ∈ xx, e.2.1≤e.1+1)
    (q : Nat → F) (n : Nat) (hq : ∀ i, 2*n≤i → q i=0)
    (a b c : F) (r : Nat) (hr : n+2≤r) : chordEven x xx q a b c r=0 := by
  have he : ∀ i, n≤i → q (2*i)=0 := by intro i hi; exact hq _ (by omega)
  have ho : ∀ i, n≤i → q (2*i+1)=0 := by intro i hi; exact hq _ (by omega)
  have xe := scatter_support_step x hx (fun i => q (2*i)) n he r (by omega)
  have xo : ∀ i, n+1≤i → scatterValue x (fun j => q (2*j+1)) i=0 := by
    intro i hi; exact scatter_support_step x hx _ n ho i hi
  have xxo := scatter_support_step xx hxx _ (n+1) xo r hr
  simp only [chordEven,hq (2*r) (by omega),hq (2*r+1) (by omega),xe,xxo,
    mul_zero,sub_self,add_zero]

theorem low_odd (x : List (ScatterEdge Nat Nat F))
    (hx : ∀ e ∈ x, e.2.1≤e.1+1)
    (q : Nat → F) (n : Nat) (hq : ∀ i, 2*n≤i → q i=0)
    (a b c : F) (r : Nat) (hr : n+1≤r) : chordOdd x q a b c r=0 := by
  have ho : ∀ i, n≤i → q (2*i+1)=0 := by intro i hi; exact hq _ (by omega)
  have xo := scatter_support_step x hx _ n ho r hr
  simp only [chordOdd,hq (2*r) (by omega),hq (2*r+1) (by omega),xo,mul_zero,add_zero]

theorem low_chord (x xx : List (ScatterEdge Nat Nat F))
    (hx : ∀ e ∈ x, e.2.1≤e.1+1) (hxx : ∀ e ∈ xx, e.2.1≤e.1+1)
    (q : Nat → F) (n : Nat) (hq : ∀ i, 2*n≤i → q i=0)
    (a b c : F) (r : Nat) (hr : 2*n+3≤r) : chordCoefficient x xx q a b c r=0 := by
  unfold chordCoefficient
  split
  · rename_i h; exact low_even x xx hx hxx q n hq a b c (r/2) (by omega)
  · exact low_odd x hx q n hq a b c (r/2) (by omega)

theorem selected_g_zero (x xx : List (ScatterEdge Nat Nat F))
    (hx : ∀ e ∈ x, e.2.1≤e.1+1) (hxx : ∀ e ∈ xx, e.2.1≤e.1+1)
    (q : Nat → F) (hq : ∀ i, 106≤i → q i=0)
    (a b c : F) (i : Fin 271) : chordCoefficient x xx q a b c (128+3*i.val)=0 := by
  exact low_chord x xx hx hxx q 53 hq a b c _ (by omega)

#print axioms low_even
#print axioms low_odd
#print axioms low_chord
#print axioms selected_g_zero
end AspisR19.LowGResidualSupport
