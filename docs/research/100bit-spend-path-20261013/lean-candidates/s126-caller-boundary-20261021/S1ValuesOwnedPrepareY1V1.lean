import S1PrepareCodecCallsV1
import S1ValuesOwnedAcceptedBytesV1
import S1NativePrepareBuffersV1
import S1AcceptedSliceRangeV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared

/-- SAME full preparation supplies its actual Y1 expansion, format dimensions,
all expanded Y1 bytes and downstream View/semantic/Prepared calls. No chosen
codec input/output, length law or independently successful child is a premise.
This is the complete owned-reference instance; native/SDK transport is separate. -/
theorem prepare_y1 (ops : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (NativeBuffers.install (withValues ops) nativeValues R B)
      D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∃ (stored initial expanded semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
      expandValues stored initial=ok (.Ok (),expanded) ∧
      stored.length=464 ∧ initial.length=928 ∧ expanded.length=928 ∧
      (∀ j, j<928 → expanded.val[j]?=
        if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8) ∧
      (NativeBuffers.install (withValues ops) nativeValues R B).op5 proof semantic y1=ok (.Ok view) ∧
      (NativeBuffers.install (withValues ops) nativeValues R B).op9 D pub view.semantic hash none=ok (.Ok sem) ∧
      (NativeBuffers.install (withValues ops) nativeValues R B).op8 D sem view hash input=ok (.Ok prepared,scratch) := by
  obtain ⟨off0,off1,off2,storedSemantic,initialSemantic,expandedSemantic,stored,initial,expanded,
    semantic,y1,view,sem,hoff0,hoff1,hoff2,hstoredSemantic,hsemantic,hstored,hvalues,hview,hsem,hnew⟩ :=
    PrepareCodecCalls.prepare_codec_calls (NativeBuffers.install (withValues ops) nativeValues R B)
      D pub proof hash prepared input scratch success
  have add1 : (16#usize+7015#usize : Result Usize)=ok 7031#usize := by
    apply UsizeArithmetic.add_eq_ok <;> scalar_tac
  have add2 : (7031#usize+464#usize : Result Usize)=ok 7495#usize := by
    apply UsizeArithmetic.add_eq_ok <;> scalar_tac
  have c1 : compact.OFF_Y1 (NativeBuffers.install (withValues ops) nativeValues R B)=ok 7031#usize := by
    unfold compact.OFF_Y1 compact.OFF_SEMANTIC
    change (do let a ← ok 16#usize;let b ← ok 7015#usize;a+b)=ok 7031#usize
    simpa only [bind_tc_ok] using add1
  have c2 : compact.OFF_INACTIVE (NativeBuffers.install (withValues ops) nativeValues R B)=ok 7495#usize := by
    unfold compact.OFF_INACTIVE
    rw [c1]
    change (do let a ← ok 7031#usize;let b ← ok 464#usize;a+b)=ok 7495#usize
    simpa only [bind_tc_ok] using add2
  have o1 : off1=7031#usize := Result.ok.inj (hoff1.symm.trans c1)
  have o2 : off2=7495#usize := Result.ok.inj (hoff2.symm.trans c2)
  subst off1
  subst off2
  have range := AspisS1AcceptedSliceRange.accepted_range proof stored 7031#usize 7495#usize hstored
  have storedSize : stored.length=464 := by scalar_tac
  change expandValues stored initial=ok (.Ok (),expanded) at hvalues
  obtain ⟨length,shape,aligned,bytes⟩ := accepted_bytes stored initial expanded hvalues
  have initialSize : initial.length=928 := by omega
  have expandedSize : expanded.length=928 := by omega
  refine ⟨stored,initial,expanded,semantic,y1,view,sem,hstored,hvalues,storedSize,
    initialSize,expandedSize,?_,hview,hsem,hnew⟩
  intro j bound
  exact bytes j (by omega)

#print axioms prepare_y1
end AspisS1ValuesOwnedInstallation
