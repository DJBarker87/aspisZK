import R0Z.BuilderModelBridge
import R0Z.BuilderModelBase
import R0Z.BuilderModelCopyBalance

/-! The builder model discharges `BuilderRefines` (LOG D46.3, D50; design §4).

* `buildModelSpec F`: the `BuilderSpec` whose 26 base columns are the model's
  columns 0..25 (in `F` by `buildModel_mem`; a classical fallback 0 is used
  only off the base premises) and whose extension columns are 0.
* `ModelRel F`: the witness premises — the Rel⁺ of D50, stated on the
  model's own digests so that a later job derives each field from
  Rspend⁺ = Rspend ∧ (transfer → change[7] ≠ 0) after build integration.
* `builderRefines_model`: `BuilderRefines (buildModelSpec F) (ModelRel F)`,
  over a field of characteristic 2^31−1.
* `builderSoundOn_model`: the resulting `BuilderSoundOn` for the honest
  prover `honestProverOf (buildModelSpec F) (ModelRel F)`. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderModel
open R0P R0Z.BuilderComplete R0Z.HonestValidity R0Z.ZkStatement

variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- Rel⁺ for the model: every premise the family and link proofs use. -/
structure ModelRel (F : Subfield K) (pub : Public K) (w : ModelWitness K) : Prop where
  pubBase : PublicBase F pub
  witBase : WitnessBase F w
  aux : AuxPremises pub w
  digest : DigestPremises pub w
  pairRight : PairRight pub w

open Classical in
/-- The model as a `BuilderSpec`. -/
def buildModelSpec (F : Subfield K) : BuilderSpec F (ModelWitness K) where
  c1 := fun pub w c r =>
    if h : buildModel pub w (Fin.castLE (by omega) c) r ∈ F then ⟨_, h⟩ else 0
  rest := fun _ _ _ _ => 0

theorem buildModelSpec_build (F : Subfield K) (pub : Public K) (w : ModelWitness K)
    (hp : PublicBase F pub) (hw : WitnessBase F w) :
    (buildModelSpec F).build pub w = buildModel pub w := by
  funext c r
  unfold BuilderSpec.build ofColumns
  split
  · rename_i hc
    show (((buildModelSpec F).c1 pub w ⟨c.val, hc⟩ r : F) : K) = _
    unfold buildModelSpec
    dsimp only
    rw [dif_pos (buildModel_mem pub w hp hw _ r)]
    rfl
  · rename_i hc
    show (0 : K) = _
    rw [buildModel, layout_high _ _ _ (by omega)]

theorem builderRefines_model [CharP K 0x7fffffff] (F : Subfield K) :
    BuilderRefines (buildModelSpec F) (ModelRel F) where
  nonCopy := fun pub w h => by
    rw [buildModelSpec_build F pub w h.pubBase h.witBase]
    exact nonCopy_model pub w h.aux h.digest
  balance := fun pub w h => by
    rw [buildModelSpec_build F pub w h.pubBase h.witBase]
    exact balance_model pub w h.pairRight

theorem builderSoundOn_model [CharP K 0x7fffffff] (hcard : 4096 < Fintype.card K)
    (F : Subfield K) (transport : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1) :
    BuilderSoundOn (honestProverOf (buildModelSpec F) (ModelRel F) transport) B x :=
  builderSoundOn_of_refines hcard _ _ (builderRefines_model F) transport B x hpub

#print axioms buildModelSpec
#print axioms buildModelSpec_build
#print axioms builderRefines_model
#print axioms builderSoundOn_model
end R0Z.BuilderModel
