import R1Z.PV_RunJoin_ChunkLift16
import R1Z.BuilderSemanticBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputLift16
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
variable {K : Type} [Field K] [CharP K 0x7fffffff]
theorem change_note (W : RustWitness) (P : RustPublic) (pub : R0P.Public K)
    (asset : liftU (K := K) P.asset = pub.assetId) (hW : WitnessOk W) :
    ∃ d, changeDR W P = ok d ∧
      DigestLift d (R0P.noteCommitment (toModel (K := K) W).changeOwner
        ((toModel (K := K) W).changeValue.val : K) pub.assetId
        (toModel (K := K) W).changeSalt) ∧ Canon8 d := by
  obtain ⟨d,hd,hl,hc⟩ := noteDigest_lift pub (toModel W) (chunksOf W P)
    (PV_RunJoin_ChunkLift16.chunks W P pub asset hW) 32 (nk 32 (by omega)) (zk _ 32 (by omega))
  refine ⟨d,hd,?_,hc⟩
  change DigestLift d (changeDigest pub (toModel (K := K) W)) at hl
  rw [BuilderSemanticBridge.changeDigest_eq] at hl
  exact hl

theorem recipient (W : RustWitness) (P : RustPublic) (pub : R0P.Public K)
    (asset : liftU (K := K) P.asset = pub.assetId) (hW : WitnessOk W)
    (hv : pub.variant = .privateTransfer) :
    ∃ d, recipDR W P = ok d ∧
      DigestLift d (R0P.noteCommitment (toModel (K := K) W).recipientOwner
        ((toModel (K := K) W).outputValue.val : K) pub.assetId
        (toModel (K := K) W).recipientSalt) ∧ Canon8 d := by
  obtain ⟨d,hd,hl,hc⟩ := noteDigest_lift pub (toModel W) (chunksOf W P)
    (PV_RunJoin_ChunkLift16.chunks W P pub asset hW) 29 (nk 29 (by omega)) (zk_tr pub 29 hv)
  refine ⟨d,hd,?_,hc⟩
  change DigestLift d (recipientDigest pub (toModel (K := K) W)) at hl
  rw [BuilderSemanticBridge.recipientDigest_eq pub _ hv] at hl
  exact hl
#print axioms change_note
#print axioms recipient
end R1Z.PV_RunJoin_OutputLift16
