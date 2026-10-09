import R0Z.ZkStatement
import R0Z.AffineLaw

/-! D4′/D4″: conditional uniform affine laws, then marginalisation over
independent eligible noise. No layout-rank, completeness, ROM or computational
assumption is installed as a premise other than the displayed MaskImage. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.Hvzk
open R0P R0Z.MaskLayout R0Z.ZkStatement
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

theorem hvzk_conditional_of_maskImage (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hm : MaskImage h B x) :
    HVZK_conditional h B outputs x := by
  intro hx w ch hw
  have hw₀ : ZkStatement.public h (Classical.choose hx) = x.1 := Classical.choose_spec hx
  obtain ⟨hr, hd⟩ := hm w (Classical.choose hx) ch hw hw₀
  have ha := AffineLaw.equal_laws_of_mask_image
    (A h B x w ch) (A h B x (Classical.choose hx) ch)
    (b h B x w ch) (b h B x (Classical.choose hx) ch) hr hd
  have hp : EqualLaws (payload h B x w ch) (payload h B x (Classical.choose hx) ch) := by
    intro v
    simpa only [← payload_affine] using ha v
  exact AffineLaw.equal_laws_const_pair _ _ (metadata outputs x ch) hp

/-- D5 independence is the product uniform tape in honestLawRun. The simulator
keeps its chosen eligible noise e₀ fixed; every honest e has the same conditional
law by D4′, so averaging over independent uniform e preserves equality. -/
theorem conditional_marginalisation (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hc : HVZK_conditional h B outputs x) :
    HVZK_perfect h B outputs x := by
  intro hx w ch hw
  apply AffineLaw.marginalisation
  intro e
  exact hc hx (w,e) ch hw

/-- Perfect interactive HVZK follows from MaskImage. Completeness is a separate
builder obligation. The statement outside the language is vacuous. -/
theorem hvzk_perfect_of_maskImage (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) : MaskImage h B x → HVZK_perfect h B outputs x := by
  intro hm
  exact conditional_marginalisation h B outputs x (hvzk_conditional_of_maskImage h B outputs x hm)

/-- The retained distance formulation has the fixed D8 value epsilon = 0. -/
theorem hvzk_zero_of_maskImage (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hm : MaskImage h B x) : HVZK h B outputs x 0 := by
  intro hx w ch hw
  exact (dist_zero_of_equalLaws _ _ (hvzk_perfect_of_maskImage h B outputs x hm hx w ch hw)).le

#print R0Z.ZkStatement.MaskImage
#print axioms hvzk_conditional_of_maskImage
#print axioms conditional_marginalisation
#print axioms hvzk_perfect_of_maskImage
#print axioms hvzk_zero_of_maskImage
end R0Z.Hvzk
