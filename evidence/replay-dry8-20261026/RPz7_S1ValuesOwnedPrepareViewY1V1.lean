import S1PrepareBothBuffersV1
import RPz7_S1WideViewY1V1
import RPz7_S1ClaimY1ReadsV1
import S1ValuesOwnedAcceptedBytesV1
import RPz7_S1NativePrepareBuffersV1
import S1AcceptedSliceRangeV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation

/-- SAME full preparation supplies its actual Y1 expansion, format dimensions,
all bytes of the SAME returned View.y1 and downstream semantic/Prepared calls. No chosen
codec input/output, length law or independently successful child is a premise.
This is the complete owned-reference instance; native/SDK transport is separate. -/
theorem prepare_view_y1 (ops : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (NativeBuffers.install (withValues ops) nativeValues R B)
      D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∃ (stored initial semantic : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
      expandValues stored initial=ok (.Ok (),view.y1) ∧
      stored.length=464 ∧ initial.length=928 ∧ view.y1.length=928 ∧
      (∀ j, j<928 → view.y1.val[j]?=
        if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8) ∧
      sourceView proof semantic view.y1=ok (.Ok view) ∧
      (NativeBuffers.install (withValues ops) nativeValues R B).op9 D pub view.semantic hash none=ok (.Ok sem) ∧
      (NativeBuffers.install (withValues ops) nativeValues R B).op8 D sem view hash input=ok (.Ok prepared,scratch) ∧
      ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
        AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧
        AspisR1CurrentPreparedClaim.Concrete.Canonical parsed := by
  have semanticLength : ∀ bytes output status updated,
      (NativeBuffers.install (withValues ops) nativeValues R B).op10 bytes output=ok (status,updated) →
        updated.length=output.length := by
    intro bytes output status updated call
    exact AspisS1NativeCompactLengths.semantic_length nativeValues bytes output updated status call
  have valueLength : ∀ bytes output status updated,
      (NativeBuffers.install (withValues ops) nativeValues R B).op11 bytes output=ok (status,updated) →
        updated.length=output.length := by
    intro bytes output status updated call
    exact length_frame bytes output updated status call
  obtain ⟨off0,off1,off2,storedSemantic,initialSemantic,expandedSemantic,stored,initial,expanded,
    semantic,y1,view,sem,hoff0,hoff1,hoff2,hstoredSemantic,hsemantic,hstored,hvalues,
    semanticEq,y1Eq,hview,hsem,hnew⟩ :=
    PrepareBothBuffers.prepare_buffers (NativeBuffers.install (withValues ops) nativeValues R B)
      semanticLength valueLength D pub proof hash prepared input scratch success
  subst semantic
  subst y1
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
  change sourceView proof expandedSemantic expanded=ok (.Ok view) at hview
  have viewY1 := sourceView_y1 proof expandedSemantic expanded view hview
  have fields := original_new_y1_fields D proof expandedSemantic expanded view sem hash prepared input scratch hview hnew
  refine ⟨stored,initial,expandedSemantic,view,sem,hstored,?_,storedSize,initialSize,?_,?_,?_,hsem,hnew,fields⟩
  · rw [viewY1]
    exact hvalues
  · rw [viewY1]
    exact expandedSize
  · intro j bound
    rw [viewY1]
    exact bytes j (by omega)
  · rw [viewY1]
    exact hview


#print axioms prepare_view_y1
end AspisS1ValuesOwnedInstallation
