import R1Z.PV_Src_PathBits

/-! Reflection of the canonical admission's selected sibling equation from K
back into the M31 carrier, with every original admission conjunct retained. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CanonicalSibling
open R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem sibling (i : BuilderCanonical.Instance (K := K)) :
    (i.val.2.path 0).2 = if (i.val.2.path 0).1 then i.val.2.pair.firstCommitment
      else i.val.2.pair.secondCommitment := by
  have h := i.property.1.2.1.sibling
  cases hb : (i.val.2.path 0).1
  · funext lane
    apply (ι : F →+* K).injective
    have hl := congrFun h lane
    simpa only [BuilderCanonical.liftWitness,hb,Bool.false_eq_true,if_false] using hl
  · funext lane
    apply (ι : F →+* K).injective
    have hl := congrFun h lane
    simpa only [BuilderCanonical.liftWitness,hb,if_true] using hl

#print axioms sibling
end R1Z.PV_Src_CanonicalSibling
