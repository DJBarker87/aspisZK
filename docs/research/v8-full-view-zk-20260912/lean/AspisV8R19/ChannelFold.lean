/- Scalar channel-fold identities and their finite dot-product lift.

This leaf is deliberately limited to commutative-ring algebra.  It does not
state any source, extraction, Fiat--Shamir, or privacy property.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace AspisR19.ChannelFold

open scoped BigOperators

variable {F : Type*} [CommRing F]

def lerp (r g beta : F) : F := r + beta * (g-r)
def p0 (qr wr : F) := qr*wr
def p1 (qr qg wr wg : F) := qr*(wg-wr)+(qg-qr)*wr
def p2 (qr qg wr wg : F) := (qg-qr)*(wg-wr)

theorem quadratic (qr qg wr wg beta : F) :
    lerp qr qg beta * lerp wr wg beta =
      p0 qr wr + beta*(p1 qr qg wr wg + beta*p2 qr qg wr wg) := by
  unfold lerp p0 p1 p2
  ring

theorem boundary (qr qg wr wg : F) :
    2*p0 qr wr + p1 qr qg wr wg + p2 qr qg wr wg = qr*wr+qg*wg := by
  unfold p0 p1 p2
  ring

theorem reconstructed_boundary (claim a c : F) :
    2*a+(claim-2*a-c)+c=claim := by
  ring

theorem affine_weights (a e h k beta : F) :
    lerp a (a+k*(h-e)) beta = a+beta*k*(h-e) := by
  unfold lerp
  ring

theorem raw_channels (all g beta : F) :
    lerp (all-g) g beta = (1-beta)*all+(2*beta-1)*g := by
  unfold lerp
  ring

theorem image_scales (tau beta : F) :
    lerp (tau^2) (tau^4) beta = tau*lerp tau (tau^3) beta := by
  unfold lerp
  ring

/- The two quotient openings can be combined before the common line-factor
   multiplication.  This is only the scalar distributive identity. -/
theorem opening_removal_bridge (s g ir ig li : F) :
    ((s-g)-ir)*li + (g-ig)*li = (s-ir-ig)*li := by
  ring

/- The channel identity lifted to a finite dot product.  The coefficient
   sums are kept outside the final affine expression, matching the
   p0/p1/p2 messages sent by the channel-fold construction. -/
theorem quadratic_dot_product {ι : Type*} (s : Finset ι)
    (qr qg wr wg : ι → F) (beta : F) :
    s.sum (fun i => lerp (qr i) (qg i) beta * lerp (wr i) (wg i) beta) =
      s.sum (fun i => p0 (qr i) (wr i)) +
        beta * (s.sum (fun i => p1 (qr i) (qg i) (wr i) (wg i)) +
          beta * s.sum (fun i => p2 (qr i) (qg i) (wr i) (wg i))) := by
  simp_rw [quadratic]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/- Linearity of an arbitrary finite weighted contraction.  The index type is
   unrestricted, so this covers four-weight blocks and any larger block. -/
theorem weighted_contraction_linearity {ι : Type*} (s : Finset ι)
    (w r g : ι → F) :
    s.sum (fun i => w i * (r i + g i)) =
      s.sum (fun i => w i * r i) + s.sum (fun i => w i * g i) := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

end AspisR19.ChannelFold

#print axioms AspisR19.ChannelFold.opening_removal_bridge
#print axioms AspisR19.ChannelFold.weighted_contraction_linearity
#print axioms AspisR19.ChannelFold.quadratic_dot_product
