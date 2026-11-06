import NIW_AlignCommon
import NIW_AlignLow
import NIW_AlignLibra
import NIG_CommonPost
import NIG_LowPost
import NIG_LibraDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignDomains
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation

theorem common (w : W) (hf : NHI_TensorOuterStep.Factors w)
 (cells : Nat → CommonCells) (logs : Nat → Common)
 (cuts : ∀ j,j<16 → cutCommon (NIT_CommonChain.row2 w) (NIT_CommonChain.row3 w) j
  (cells j) (logs j) (cells (j+1)))
 (laws : ∀ j,j<16 → QMul (logs j).lhs (logs j).rhs (logs j).reply)
 (initial : NHI_CellCanon.array (cells 0)) : NHI_CellCanon.array (cells 16) := by
 exact (NIG_CommonPost.source w hf (cells 0) initial (w,cells 16)
  (NIW_AlignCommon.emitted w hf cells logs cuts laws).2).2

theorem low (ap0 ap1 : Powers) (cells : Nat → LowCells) (logs : Nat → Low)
 (cuts : ∀ j,j<16 → cutLow ap0 ap1 j (cells j) (logs j) (cells (j+1)))
 (laws : ∀ j,j<16 → EMul (logs j).a (logs j).b (logs j).product)
 (scales : ∀ j,j<16 → NIT_LowInterpretation.Scale (logs j).scale_a (logs j).scaled)
 (c0 : canonical ap0) (c1 : canonical ap1) (initial : canonical (cells 0)) : canonical (cells 16) :=
 NIG_LowPost.source ap0 ap1 c0 c1 (cells 0) (cells 16) initial
  (NIW_AlignLow.emitted ap0 ap1 cells logs cuts laws scales).2

/-- Actual Libra stream postcondition on all results; unentered suffixes carry
no domain requirement and a failing/diverging stream is not made returning. -/
theorem libra (f : Ref (Slice U8)) (weights : Powers)
 (cells : Nat → Parts) (logs : Nat → Result LibraLog)
 (association : NIW_AlignLibra.Association f weights cells logs)
 (cw : canonical weights) (initial : canonical (cells 0)) :
 NIT_LibraChain.Post (NIW_AlignLibra.run cells logs 4 0) := by
 have source := (NIW_AlignLibra.emitted f weights cells logs association).2
 cases observed : NIW_AlignLibra.run cells logs 4 0 with
 | fail e=>trivial
 | div=>trivial
 | ok parts=>
  rw [observed] at source
  exact NIG_LibraDomain.source f.value weights cw (cells 0) parts initial source

#print axioms common
#print axioms low
#print axioms libra
end AspisR1.NIW_AlignDomains
