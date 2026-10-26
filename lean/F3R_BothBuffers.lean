import PSem_SourceCuts
import F3R_PrepareBuffers
import SdkD_PrepareSource
import S1PrepareBothBuffersV1
import S1WideViewY1V1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3R_BothBuffers
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation

theorem on_run {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    ∃ (stored initial expanded storedY1 initialY1 y1 : Slice U8) (view : verifier.View)
      (sem : r1_semantic.Verified H),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=16#usize,«end»:=7031#usize}=ok stored ∧
      AspisS1NativeCompact.compact.expand_semantic nativeValues stored initial=ok (.Ok (),expanded) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7031#usize,«end»:=7495#usize}=ok storedY1 ∧
      expandValues storedY1 initialY1=ok (.Ok (),y1) ∧
      sourceView proof expanded y1=ok (.Ok view) ∧ view.semantic=expanded ∧ view.y1=y1 ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (ClaimsUnrolledFinish.install std B) D pub expanded hash=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        D sem view hash (Array.repeat 29#usize run.zero)=ok (.Ok run.p,run.scratch) ∧
      AspisR1PublicPreparation.PreparedHashCode.observe
        (AspisR1PublicPreparation.PreparedHashCode.run (SdkD_PrepareSource.code (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo))) B std D pub proof hash
          (Array.repeat 29#usize run.zero))).1=
        AspisR1PublicPreparation.PreparedHashCode.observe
          (AspisR1PublicPreparation.PreparedHashCode.run (S1SemanticCodeInstallation.code
            AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B) D pub view.semantic hash)).1 ++
        AspisR1PublicPreparation.PreparedHashCode.observe
          (AspisR1PublicPreparation.PreparedHashCode.run (closedPreparationCode D sem view hash
            (Array.repeat 29#usize run.zero))).1 := by
  let installed := Tx1Q_Execution.actual ops reserved query geo B std
  have semanticLength : ∀ input output status updated,
      installed.op10 input output=ok (status,updated) → updated.length=output.length := by
    intro input output status updated call
    exact AspisS1NativeCompactLengths.semantic_length nativeValues input output updated status call
  have valueLength : ∀ input output status updated,
      installed.op11 input output=ok (status,updated) → updated.length=output.length := by
    intro input output status updated call
    exact length_frame input output updated status call
  have erased := (SdkD_PrepareSource.source (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo))) B std D pub proof hash (Array.repeat 29#usize run.zero)).trans run.prepare_call
  obtain ⟨semantic,y1,view,sem,wide,semanticCode,originalCode,logs,
    off0,off1,off2,stored,initial,expanded,storedY1,initialY1,expandedY1,
    h0,h1,h2,read,expand,readY1,expandY1,semanticEq,y1Eq⟩ :=
    F3R_PrepareBuffers.reached (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo))) AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)
      D pub proof hash run.p (Array.repeat 29#usize run.zero) run.scratch
      (fun input output status updated call=>AspisS1NativeCompactLengths.semantic_length nativeValues input output updated status call)
      (fun input output status updated call=>length_frame input output updated status call) erased
  have verify := (S1SemanticCodeInstallation.source AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub view.semantic hash).symm.trans semanticCode
  have prepare := (closedPreparationCode_erasure D sem view hash (Array.repeat 29#usize run.zero)).symm.trans originalCode
  have c0 : compact.OFF_SEMANTIC installed=ok 16#usize := by unfold compact.OFF_SEMANTIC;rfl
  have add1 : (16#usize+7015#usize : Result Usize)=ok 7031#usize := by
    apply UsizeArithmetic.add_eq_ok <;> scalar_tac
  have c1 : compact.OFF_Y1 installed=ok 7031#usize := by
    unfold compact.OFF_Y1
    rw [c0]
    change (do let a ← ok 16#usize;let b ← ok 7015#usize;a+b)=_
    simpa only [bind_tc_ok] using add1
  have add2 : (7031#usize+464#usize : Result Usize)=ok 7495#usize := by
    apply UsizeArithmetic.add_eq_ok <;> scalar_tac
  have c2 : compact.OFF_INACTIVE installed=ok 7495#usize := by
    unfold compact.OFF_INACTIVE
    rw [c1]
    change (do let a ← ok 7031#usize;let b ← ok 464#usize;a+b)=_
    simpa only [bind_tc_ok] using add2
  have eq0 := Result.ok.inj (h0.symm.trans c0)
  have eq1 := Result.ok.inj (h1.symm.trans c1)
  have eq2 := Result.ok.inj (h2.symm.trans c2)
  subst off0;subst off1;subst off2;subst semantic;subst y1
  change sourceView proof expanded expandedY1=ok (.Ok view) at wide
  have semEq := sourceView_semantic proof expanded expandedY1 view wide
  have yEq := sourceView_y1 proof expanded expandedY1 view wide
  change S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub view.semantic hash=ok (.Ok sem) at verify
  rw [semEq] at verify
  exact ⟨stored,initial,expanded,storedY1,initialY1,expandedY1,view,sem,
    read,expand,readY1,expandY1,wide,semEq,yEq,verify,prepare,logs⟩

#print axioms on_run
end AspisR1.F3R_BothBuffers
end
