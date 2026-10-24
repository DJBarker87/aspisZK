import S1CurrentPrepareCausalV1
import S1ValuesOwnedStage1Y1V1
set_option autoImplicit false
noncomputable section
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1PublicPreparation.PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- One accepted owned stage1 supplies decoded public reuse, physical roots,
Y1 domain, full prepare oracle effects, identical Prepared/gamma scratch and
checkpoint continuation. Native SDK and lower primitive ports remain open. -/
theorem owned_stage1_effects (adapterOps : AdapterRw.Ops) (ops : Ops)
   
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (sha : Bytes → Array U8 32#usize)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install (installP3Adapter adapterOps sha) (NativeBuffers.install (withValues ops) nativeValues R B))
      program accounts data=ok (.Ok out)) :
    ∃ (bytes proof : Slice U8) (split : Usize)
      (statement : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok statement) ∧
      split=compact.SPLIT ∧
      ∃ (zero : aspis_core.field.wide_exact.WideExact) (prepared : verifier.Prepared)
        (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (root0 root1 : Array U8 32#usize),
        verifier.candidate.prepare (NativeBuffers.install (withValues ops) nativeValues R B) (p3CallerDigest sha)
          (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
          proof () none (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
        prepared.roots=Array.make 2#usize [root0,root1] ∧ root0.val=proof.val.slice 16 48 ∧ root1.val=proof.val.slice 63 95 ∧
        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues R B) (p3CallerDigest sha)
          bytes proof split () none prepared scratch=ok (.Ok out) ∧
        eval (fun bytes => decodeState (sha bytes))
          (S1PrepareCode.program ops R B
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
            proof () (Array.repeat 29#usize zero))=
          (observe (run (S1PrepareCode.prepare ops R B (p3CallerDigest sha)
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
            proof () (Array.repeat 29#usize zero))).1,ok (.Ok prepared,scratch)) ∧
        ∃ stored initial expanded : Slice U8,
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
            proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
          expandValues stored initial=ok (.Ok (),expanded) ∧
          stored.length=464 ∧ initial.length=928 ∧ expanded.length=928 ∧
          ∀ j, j<928 → expanded.val[j]?=
            if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8 := by
  obtain ⟨bytes,proof,split,statement,decoded,hk,zero,prepared,scratch,root0,root1,
    hprepare,hroots,hphysical0,hphysical1,tail,stored,initial,expanded,hstored,hvalues,
    storedSize,initialSize,expandedSize,formula⟩ :=
    owned_stage1_y1 (installP3Adapter adapterOps sha) ops R B program accounts data out accepted
  have digestEq : NativeBuffers.callerDigest (installP3Adapter adapterOps sha)
      (withValues ops) nativeValues R B=p3CallerDigest sha := rfl
  rw [digestEq] at hprepare tail
  refine ⟨bytes,proof,split,statement,decoded,hk,zero,prepared,scratch,root0,root1,
    hprepare,hroots,hphysical0,hphysical1,tail,?_,
    stored,initial,expanded,hstored,hvalues,storedSize,initialSize,expandedSize,formula⟩
  rw [S1PrepareCode.causal_exact,hprepare]

#print axioms owned_stage1_effects
end AspisS1ValuesOwnedInstallation
