import PRVEq_CallerPrepTx1DeployedNOC_o1
import NOC_PrepareConv
import NOC_Tx1Conv
import NOC_Tx1Forward
import NOC_PrepareFront
set_option autoImplicit false
noncomputable section
/-! PCVP_ composition at the corrected seed.  The fresh frozen PCVK_C_o1 prepare/tx1 (4bb3b3f emission) at
xOf (currentInstalled (NOC_HostCtx.configuration c)) equals the gate prepare/tx1 at that Ops (PCVP_C.noc_prepare/noc_tx1,
conditional on the Bound callee fields being instantiated by the deployed slots: organisation, not discharge).
Hence the existing forward/converse theorems NOC_PrepareFront.source, NOC_PrepareConv.prepare, NOC_Tx1Forward.source,
NOC_Tx1Conv.tx1 (all stated at `cur c`) hold verbatim for the fresh frozen definitions.  Domains are those of the cited theorems. -/
namespace AspisR1.PCVP_CComp
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

abbrev curN {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := PCVP_C.curN c

theorem fresh_prepare_forward {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (pub : NNH_Libraries.VL.Public) (proof : Slice U8)
    (g g' : LIB_VCarriers.E29) (prep : LIB_VCarriers.Prepared) (width : proof.val.length = 57607)
    (called : NNH_Tx1Returns.preparedValue ⟨pub, LIB_Carriers.bytes proof, g⟩ (NOC_Run5bCtx.envOf c) = .ok (prep, g')) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.prepare (PCVP_C.xOf (curN c)) _ (NNV_PreparedAtHost.digest c)
      (FirstComposition.toCurrentPublic pub) proof () none (NNV_PreparedInputs.scratch g) =
    .ok (.Ok (InstalledPreparation.currentPrepared prep), NNV_PreparedInputs.scratch g') := by
  rw [PCVP_C.noc_prepare c]
  exact NOC_PrepareFront.source c pub proof g g' prep width called

theorem fresh_prepare_converse {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (pub : NNH_Libraries.VL.Public) (proof : Slice U8)
    (width : proof.val.length = 57607) (digest : LIB_VPublicDomain.publicDigestDom pub)
    (called : ∃ p' g1, @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.prepare (PCVP_C.xOf (curN c)) _ (NNV_PreparedAtHost.digest c)
      (FirstComposition.toCurrentPublic pub) proof () none (NNV_PreparedInputs.scratch LIB_Instances.VL.zeroE29) = .ok (.Ok p', g1)) :
    ∃ pg, NNH_Tx1Returns.preparedValue ⟨pub, LIB_Carriers.bytes proof, LIB_Instances.VL.zeroE29⟩ (NOC_Run5bCtx.envOf c) = .ok pg := by
  rw [PCVP_C.noc_prepare c] at called
  exact NOC_PrepareConv.prepare c pub proof width digest called

theorem fresh_tx1_converse {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (a : RSL.TX1_094.Args NNH_Tx1Returns.V) (pubBytes proof : Slice U8)
    (hproof : a.proof = LIB_Carriers.bytes proof) (hk : a.k = 10) (width : proof.val.length = 57607)
    (digest : LIB_VPublicDomain.publicDigestDom a.public_)
    (called : ∃ v, @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.tx1 (PCVP_C.xOf (curN c)) _ (NNV_PreparedAtHost.digest c)
      (FirstComposition.toCurrentPublic a.public_) pubBytes proof 10#usize () none = .ok (.Ok v)) :
    ∃ out, NNH_Tx1Returns.value a (NOC_Run5bCtx.envOf c) = .ok out := by
  rw [PCVP_C.noc_tx1 c] at called
  exact NOC_Tx1Conv.tx1 c a pubBytes proof hproof hk width digest called

theorem fresh_tx1_forward {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (a : RSL.TX1_094.Args NNH_Tx1Returns.V)
    (pubBytes proof : Slice U8) (k : Usize) (hpub : a.public_bytes = LIB_Carriers.bytes pubBytes)
    (hproof : a.proof = LIB_Carriers.bytes proof) (hk : a.k = k.val) (width : proof.val.length = 57607)
    (out : RSL.Bytes) (called : NNH_Tx1Returns.value a (NOC_Run5bCtx.envOf c) = .ok out) :
    ∃ v : alloc.vec.Vec U8,
      @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.tx1 (PCVP_C.xOf (curN c)) _ (NNV_PreparedAtHost.digest c)
        (FirstComposition.toCurrentPublic a.public_) pubBytes proof k () none = .ok (.Ok v) ∧
      LIB_Carriers.bytes (alloc.vec.Vec.deref v) = out := by
  rw [PCVP_C.noc_tx1 c]
  exact NOC_Tx1Forward.source c a pubBytes proof k hpub hproof hk width out called

#print axioms fresh_tx1_forward
#print axioms fresh_prepare_forward
#print axioms fresh_prepare_converse
#print axioms fresh_tx1_converse
end AspisR1.PCVP_CComp
end
