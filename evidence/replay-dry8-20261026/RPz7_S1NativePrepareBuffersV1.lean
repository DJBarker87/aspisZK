import S1PrepareExpansionBuffersV1
import RPz7_S1WideViewSemanticV1
import RPz7_S1PrepareSemanticRootsV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open OriginalSerializerInstallation

def install (ops : Ops) (native : AspisS1NativeCompact.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : Ops :=
  closedInstall (S1SemanticInstallation.install
    {ops with op10:=AspisS1NativeCompact.compact.expand_semantic native} R B)

/-- The same complete preparation return binds the physical compact slice,
unchanged native expansion, actual buffer reconstruction, source View,
semantic verification and original Prepared::new on its returned scratch.
The sole remaining buffer law is explicitly the Y1 expand-values length law;
no semantic-expansion law, chosen View/semantic object or child success is assumed. -/
theorem prepare_buffers (ops : Ops) (native : AspisS1NativeCompact.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (valueLength : ∀ input output status updated,
      ops.op11 input output=ok (status,updated) → updated.length=output.length)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (install ops native R B)
      D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∃ (stored initial expanded y1 : Slice U8) (view : verifier.View)
      (sem : r1_semantic.Verified H),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=16#usize,«end»:=7031#usize}=ok stored ∧
      AspisS1NativeCompact.compact.expand_semantic native stored initial=ok (.Ok (),expanded) ∧
      sourceView proof expanded y1=ok (.Ok view) ∧ view.semantic=expanded ∧
      S1SemanticInstallation.verify R B D pub expanded hash=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        D sem view hash input=ok (.Ok prepared,scratch) := by
  have semanticLength : ∀ bytes output status updated,
      (install ops native R B).op10 bytes output=ok (status,updated) → updated.length=output.length := by
    intro bytes output status updated call
    change AspisS1NativeCompact.compact.expand_semantic native bytes output=ok (status,updated) at call
    exact AspisS1NativeCompactLengths.semantic_length native bytes output updated status call
  have y1Length : ∀ bytes output status updated,
      (install ops native R B).op11 bytes output=ok (status,updated) → updated.length=output.length := by
    intro bytes output status updated call
    change ops.op11 bytes output=ok (status,updated) at call
    exact valueLength bytes output status updated call
  obtain ⟨off0,off1,stored,initial,expanded,semantic,y1,view,sem,
    hoff0,hoff1,hstored,hexpanded,sameSemantic,hview,hsem,hnew⟩ :=
    PrepareBuffers.prepare_buffers (install ops native R B) semanticLength y1Length
      D pub proof hash prepared input scratch success
  have c0 : compact.OFF_SEMANTIC (install ops native R B)=ok 16#usize :=
    by unfold compact.OFF_SEMANTIC; rfl
  have c1 : compact.OFF_Y1 (install ops native R B)=ok 7031#usize :=
    by
      have add : (16#usize+7015#usize : Result Usize)=ok 7031#usize := by
        apply UsizeArithmetic.add_eq_ok <;> scalar_tac
      unfold compact.OFF_Y1 compact.OFF_SEMANTIC
      change (do let a ← ok 16#usize; let b ← ok 7015#usize; a+b)=ok 7031#usize
      simpa only [bind_tc_ok] using add
  have off0Eq := Result.ok.inj (c0.symm.trans hoff0)
  have off1Eq := Result.ok.inj (c1.symm.trans hoff1)
  subst off0
  subst off1
  subst semantic
  change AspisS1NativeCompact.compact.expand_semantic native stored initial=ok (.Ok (),expanded) at hexpanded
  change sourceView proof expanded y1=ok (.Ok view) at hview
  have retainedSemantic := sourceView_semantic proof expanded y1 view hview
  change S1SemanticInstallation.verify R B D pub view.semantic hash=ok (.Ok sem) at hsem
  rw [retainedSemantic] at hsem
  change originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
    D sem view hash input=ok (.Ok prepared,scratch) at hnew
  exact ⟨stored,initial,expanded,y1,view,sem,hstored,hexpanded,hview,retainedSemantic,hsem,hnew⟩

#print axioms prepare_buffers
end AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers
