import R1Z.PV_RunJoin_ChunkLift16
import R1Z.BuilderSemanticBridge
import R1Z.PV_RunJoin_FixtureInputCommitment
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LeafLift16
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
variable {K : Type} [Field K] [CharP K 0x7fffffff]
theorem input (W : RustWitness) (P : RustPublic) (pub : R0P.Public K)
    (asset : liftU (K := K) P.asset = pub.assetId) (hW : WitnessOk W) :
    ∃ d, inputLeafR W P = ok d ∧
      DigestLift d (R0P.noteCommitment (R0P.ownerKey (toModel (K := K) W).sk)
        ((toModel (K := K) W).inputValue.val : K) pub.assetId (toModel (K := K) W).salt) ∧ Canon8 d := by
  obtain ⟨d,hd,hl,hc⟩ := noteDigest_lift pub (toModel (K := K) W) (chunksOf W P)
    (PV_RunJoin_ChunkLift16.chunks W P pub asset hW) 3 (nk 3 (by omega)) (zk _ 3 (by omega))
  refine ⟨d,hd,?_,hc⟩
  change DigestLift d (inputLeaf pub (toModel (K := K) W)) at hl
  rw [BuilderSemanticBridge.inputLeaf_eq] at hl
  exact hl

theorem word_injective {a b : U32} (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (h : liftU (K := PV_RunJoin_FixtureRecords.M) a = liftU (K := PV_RunJoin_FixtureRecords.M) b) : a = b := by
  apply UScalar.eq_of_val_eq
  exact CharP.natCast_injOn_Iio PV_RunJoin_FixtureRecords.M 2147483647 ha hb h

#print axioms input
#print axioms word_injective
end R1Z.PV_RunJoin_LeafLift16
