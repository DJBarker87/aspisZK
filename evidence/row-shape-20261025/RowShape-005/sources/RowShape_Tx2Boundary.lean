import RowShape_InstalledSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.RowShape_Tx2Boundary
open AspisR1CurrentCaller

/-- The Claims SDK installation replaces TX1 and codec slots, but retains the
entire supplied authenticated TX2 child. It does not install its inner parser
or scan. This is the exact sdkOps used by accepted_pair_claims. -/
theorem authenticated_tx2_slot (adapterOps : AdapterRw.Ops) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) :
    (ClaimsUnrolledSdk.sdkOps adapterOps ops B std).op11 = adapterOps.op11 := rfl

/-- On the SAME f,s cut witnesses supplied by D189, the actual TX2 dispatch
remains the supplied child. This theorem chooses no new execution or cut. -/
theorem same_cut_tx2 (adapterOps : AdapterRw.Ops) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapterOps ops B std) accounts1 accounts2 saved f s) :
    adapterOps.op11
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
        (ClaimsUnrolledSdk.sdkOps adapterOps ops B std))
      s.pub s.proof s.checkpoint () none = Aeneas.Std.Result.ok (.Ok ()) :=
  cuts.second

#print axioms authenticated_tx2_slot
#print axioms same_cut_tx2
end AspisR1.RowShape_Tx2Boundary
end
