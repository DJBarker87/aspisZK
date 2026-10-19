import InitialMessageForwardFilterV3
import Mathlib.Algebra.CharP.Algebra

set_option autoImplicit false
namespace AspisWide.InitialMessagePublicFilter
open CompPoly AspisWide.InitialForwardEncoderBaseV9
open AspisWide.InitialMessageForwardFilterV3

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [LawfulBEq (CPolynomial K)]

/-- No public-node hypotheses remain: the admitted algebra structure already
forces M31 characteristic, and the two small node counts are below M31. -/
theorem filterPublic_complete (m : Fin 1024 → K) :
    filterPublic (encodeInitialC m) = some m := by
  letI : CharP K AspisCircleGroupOrder.P :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod AspisCircleGroupOrder.P) K)
      AspisCircleGroupOrder.P (by norm_num [AspisCircleGroupOrder.P])
  exact filterPublic_complete_on_image
    (by norm_num [AspisCircleGroupOrder.P])
    (by norm_num [AspisCircleGroupOrder.P]) m

theorem filterPublic_sound (q : CPolynomial K) (m : Fin 1024 → K)
    (h : filterPublic q = some m) : encodeInitialC m = q :=
  filterMessage_sound publicNodes0 publicNodes1 q m h

#print axioms filterPublic_complete
#print axioms filterPublic_sound
end AspisWide.InitialMessagePublicFilter
