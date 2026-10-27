import RPz7_SdkD_FoldedCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_PrepareProvenance
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation

/-- Immutable roots and semantic source provenance on the actual installed
preparation return. This conclusion is not SessionAPrepare assumed again. -/
theorem roots (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input = ok (.Ok p,scratch)) :
    p.variant = .S2 ∧
    ∃ (semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H)
      (pre : AspisR1PublicPreparation.r1_wire.Prefix) (payload : Slice U8) (root : Array U8 32#usize),
      sourceView proof semantic y1 = ok (.Ok view) ∧
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted view.semantic = ok (.Ok pre) ∧
      AspisR1PublicPreparation.FinishModel.payload pre 2#u8 = ok (.Ok payload) ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload = ok (.Ok root) ∧
      root.val = payload.val ∧ p.roots = Array.make 2#usize [pre.c1_root,root] ∧
      p.semantic_alpha = sem.alpha ∧ p.z = sem.z := by
  obtain ⟨variant,semantic,y1,view,sem,pre,initial,after,challenges,payload,root,
    hview,hsem,hnew,hparse,hpublic,hbegin,hfinish,hpayload,hcopy,hbytes,hroots,halpha,hz,hcan⟩ :=
    prepare_semantic_roots
      {withValues ops with op10 := AspisS1NativeCompact.compact.expand_semantic nativeValues}
      AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)
      D pub proof hash p input scratch success
  exact ⟨variant,semantic,y1,view,sem,pre,payload,root,hview,hparse,hpayload,hcopy,hbytes,hroots,halpha,hz⟩

#print axioms roots
end AspisR1.SdkD_PrepareProvenance
end
