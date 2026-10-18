import R1Z.IIPrimeR1
import R1Z.ClauseIR1
import R0Z.HonestValidity
import R0Z.HvzkV

/-! J0c item 1 (LOG D40.3): `MaskImageOn P_R1` on the per-challenge valid sets.
`maskImageOnV_R1_valid` on `{w | HonestValid x.1 B (h.build w) ch}`;
`maskImageOnV_R1` on the pole-free set `VR1` (the prover's attempt acceptance)
for builder-sound instances; `hvzk_R1V : HVZK_onV P_R1 h VR1`. -/
set_option autoImplicit false
noncomputable section

namespace R1Z.MaskImageVR1
open R0P R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort R0Z.HvzkV
  R1Z.Batched R1Z.PredicateR1
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### The per-challenge valid sets -/

/-- Validity at the challenge, for instances of the statement. -/
def VValid (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle) :
    Challenges K → h.Instance → Prop :=
  fun ch w => h.public w = x.1 → R0Z.HonestValid.HonestValid x.1 B (h.build w) ch

/-- The prover's attempt acceptance beyond `P_R1`: no LogUp pole. -/
def VR1 (h : HonestProver K) : Challenges K → h.Instance → Prop :=
  fun ch w => R0Z.HonestValidity.NoPole (h.build w) (ch.sem 0) (ch.sem 1)

theorem maskImageOnV_R1_valid (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hF : ∀ w, h.public w = x.1 → BaseTyped F (h.build w)) :
    MaskImageOnV (Bat := R1Bat) (P_R1 h.transport B hB) h (VValid h B x) B x :=
  ⟨fun ch hP w n _ hw => R1Z.ClauseIR1.clause_i_R1_all h B hB x hpub hF ch hP w n hw,
    fun ch hP w w' hv hv' hw hw' => R1Z.IIPrimeR1.cTilde_sub_mem_range_R1 h B hB x hpub ch hP w w'
      (hF w hw) (hF w' hw') (hv hw) (hv' hw')⟩

theorem maskImageOnV_R1 (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x) :
    MaskImageOnV (Bat := R1Bat) (P_R1 h.transport B hB) h (VR1 h) B x :=
  maskImageOnV_mono _ h (VR1 h) (VValid h B x) B x
    (fun ch w _ hv hw => R0Z.HonestValidity.honestValid_of x.1 B (h.build w) ch (hs w hw) hv)
    (maskImageOnV_R1_valid h B hB x hpub (R0Z.HonestValidity.baseTyped_of h B x hs))

theorem hvzk_R1V (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x) :
    HVZK_onV (Bat := R1Bat) (P_R1 h.transport B hB) h (VR1 h) B outputs x :=
  hvzk_on_of_V _ h _ B outputs x (maskImageOnV_R1 h B hB x hpub hs)

#print axioms VValid
#print axioms VR1
#print axioms maskImageOnV_R1_valid
#print axioms maskImageOnV_R1
#print axioms hvzk_R1V
end R1Z.MaskImageVR1
