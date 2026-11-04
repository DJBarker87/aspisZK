import R0Z.HonestValidity
import R0Z.HelperInactive
import R0Z.HelperSum

/-! J0b assembly (LOG D40.2, D42.4): of the four fields of
`HonestBuilderSound`, `helperInactive` holds for every trace
(`HelperInactive.helperInactive`, a registry fact) and `helperSum` holds for
every trace with `CopyLinkBalance` (`HelperSum.helperSum_of_balance`, from the
CopyRegistry (row, slot) Nodup facts).  What remains of the builder is
`HonestBuilderCore`: base typing, the 28 non-copy production lanes, and
`CopyLinkBalance pub t` on the raw instance trace `t = h.build w` — every
enabled copy link's producer tuple equals its consumer tuple.  This last field
is genuinely about the builder (it says the builder writes the copied cells
consistently); no registry fact implies it. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderSound
open R0P R0P.Sumcheck R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12
open R0Z.HonestValidity

attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- The builder obligations left after J0b's two helper sums are discharged. -/
structure HonestBuilderCore (F : Subfield K) (pub : Public K) (B : PackBasis F) (t : Trace K) :
    Prop where
  baseTyped : BaseTyped F t
  lanes : ∀ (lam chi : K) (i : Fin 29) (b : Fin 10 → Bool), i.val < 28 → laneOf t pub lam chi B i b = 0
  balance : CopyLinkBalance pub t

theorem honestBuilderSound_of_core (pub : Public K) (B : PackBasis F) (t : Trace K)
    (hc : HonestBuilderCore F pub B t) : HonestBuilderSound F pub B t :=
  ⟨hc.baseTyped, hc.lanes, R0Z.HelperSum.helperSum_of_balance pub t hc.balance,
    fun lam chi => R0Z.HelperInactive.helperInactive pub t lam chi⟩

/-- The prover-level form. -/
def BuilderCoreOn (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle) : Prop :=
  ∀ w, h.public w = x.1 → HonestBuilderCore F x.1 B (h.build w)

theorem builderSoundOn_of_core (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) (hc : BuilderCoreOn h B x) : BuilderSoundOn h B x :=
  fun w hw => honestBuilderSound_of_core x.1 B (h.build w) (hc w hw)

#print axioms HonestBuilderCore
#print axioms honestBuilderSound_of_core
#print axioms BuilderCoreOn
#print axioms builderSoundOn_of_core
end R0Z.BuilderSound
