/- Arithmetic bridge for the actual six disclosed first-relation coefficients.
   This does not assert existence of a source witness correction, an oracle
   law, extraction, or privacy. In particular beta is unrestricted. -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace AspisR19.FirstRelationBoundary
variable {F : Type*} [Field F]

/- accumulate_chunk uses [b0,b3,b2,b1]/4; only c0,c4 enter boundary_sum. -/
theorem chunk_boundary (a0 a1 a2 a3 b0 b1 b2 b3 : F)
    (hfour : (4:F) ≠ 0) :
    4*(a0*b0/4+(a1*b1+a2*b2+a3*b3)/4) =
      a0*b0+a1*b1+a2*b2+a3*b3 := by
  calc
    _ = (a0*b0+(a1*b1+a2*b2+a3*b3))*(4*(4:F)⁻¹) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [mul_inv_cancel₀ hfour, mul_one]; ring

/- r0=<rq,wr>, r1=<rq,wg>, g0=<qg,wr>, g1=<qg,wg>.
   scale is gamma^27; p2 preservation is scale*(g1-g0)-(r1-r0)=0. -/
theorem boundary_identity (r0 r1 g0 g1 scale beta : F) :
    (1-beta)*((1-beta)*r0+beta*r1) +
      scale*beta*((1-beta)*g0+beta*g1) =
    (1-beta)*r0+beta*scale*g1-
      beta*(1-beta)*(scale*(g1-g0)-(r1-r0)) := by ring

theorem boundary_zero (r0 r1 g0 g1 scale beta : F)
    (hp0 : r0=0) (hg : g1=0)
    (hp2 : scale*(g1-g0)-(r1-r0)=0) :
    (1-beta)*((1-beta)*r0+beta*r1) +
      scale*beta*((1-beta)*g0+beta*g1) = 0 := by
  rw [boundary_identity, hp2, hp0, hg]
  ring

theorem missing_four (c0 c4 : F) (hfour : (4:F) ≠ 0)
    (h0 : c0=0) (hb : 4*(c0+c4)=0) : c4=0 := by
  have h := (mul_eq_zero.mp hb).resolve_left hfour
  simpa only [h0, zero_add] using h

theorem source_quarter : (4*(536870912:Nat)) % 2147483647 = 1 := by norm_num

/- The source G functional on legal qvector tails. The source dual/chord
   correspondence is an external premise, not asserted by this leaf. -/
theorem structured_moment_zero (inactive h point1 point2 k t tt b c x : F)
    (hi : inactive=0) (hh : h=0) (h1 : point1=0) (h2 : point2=0) :
    inactive+k*h+k^2*point1+k^3*point2+t*0+tt*(b*(c*x)-c*(b*x))=0 := by
  rw [hi, hh, h1, h2]
  ring

theorem all_seven (d : Fin 7 → F) (hfour : (4:F)≠0)
    (sent : ∀ i, i≠4 → d i=0) (hb : 4*(d 0+d 4)=0) : ∀ i, d i=0 := by
  have h4 := missing_four (d 0) (d 4) hfour (sent 0 (by decide)) hb
  intro i
  by_cases h : i=4
  · simpa only [h] using h4
  · exact sent i h

/- At beta=0 the source G coefficient rows vanish. A fixed nonzero R
   coefficient then cannot be cancelled by any G value or gamma scale.
   This does not claim that such an R correction occurs at an admissible
   source prefix, or rule out a different H1/R correction. -/
theorem zero_beta_obstruction (r g scale : F) (hr : r≠0) :
    (1-(0:F))*r+scale*((0:F)*g) ≠ 0 := by
  simpa only [sub_zero, one_mul, zero_mul, mul_zero, add_zero] using hr

#print axioms chunk_boundary
#print axioms boundary_identity
#print axioms boundary_zero
#print axioms missing_four
#print axioms source_quarter
#print axioms structured_moment_zero
#print axioms all_seven
#print axioms zero_beta_obstruction
end AspisR19.FirstRelationBoundary
