import FIp_CircleValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_CircleMade
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof SAQ_LineSource
theorem made (alpha a b c d out : E) (ix iy lx ly lz : U32)
    (run : FIp_CircleSource.circle alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out) :
    CanonicalWide out ∧ decodeWide out=FIp_CircleValue.formula (decodeWide alpha)
      (decodeWide a) (decodeWide b) (decodeWide c) (decodeWide d) (decodeBase ix) (decodeBase iy) := by
  obtain ⟨cut⟩ := FIp_CircleCuts.cuts alpha a b c d out ix iy lx ly lz run
  exact FIp_CircleValue.on_cuts alpha a b c d out ix iy cut
#print axioms made
end AspisR1.FIp_CircleMade
end
