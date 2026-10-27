import R1Z.PV_RunJoin_LeafLift16
import R1Z.PV_RunJoin_FixtureNullifier
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NullifierLift16
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
variable {K : Type} [Field K] [CharP K 0x7fffffff]
theorem nullifier (W : RustWitness) (P : RustPublic) (pub : R0P.Public K)
    (asset : liftU (K := K) P.asset = pub.assetId) (hW : WitnessOk W) :
    ∃ d, noteDigestR (chunksOf W P) 26 = ok d ∧
      DigestLift d (R0P.nullifierHash (toModel (K := K) W).sk
        (toModel (K := K) W).salt) ∧ Canon8 d := by
  obtain ⟨d,hd,hl,hc⟩ := noteDigest_lift pub (toModel W) (chunksOf W P)
    (PV_RunJoin_ChunkLift16.chunks W P pub asset hW) 26 (nk 26 (by omega)) (zk _ 26 (by omega))
  refine ⟨d,hd,?_,hc⟩
  change DigestLift d (nullifierDigest (toModel (K := K) W)) at hl
  rw [BuilderSemanticBridge.nullifierDigest_eq pub] at hl
  exact hl
#print axioms nullifier
end R1Z.PV_RunJoin_NullifierLift16
