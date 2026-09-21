/- UNCOMPILED research draft. Scalar leaves, not source/extraction/FS/privacy. -/
import Mathlib.Tactic.Ring
namespace AspisR19.ChannelFold
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
theorem reconstructed_boundary (claim a c : F) : 2*a+(claim-2*a-c)+c=claim := by ring
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
end AspisR19.ChannelFold
