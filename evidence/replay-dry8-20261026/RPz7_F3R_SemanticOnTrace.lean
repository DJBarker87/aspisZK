import RPz7_F3R_VerifyLog
import RPz7_F3R_TraceUnique
import RPz7_F3R_InitUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_SemanticOnTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog SourceGlobalOracleInitial

theorem log (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 Unit)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (sem : r1_semantic.Verified Unit)
    (success : erase (S1SemanticCode.verify (S1SemanticCode.finish R B) D pub bytes () none)=ok (.Ok sem))
    (pre : r1_wire.Prefix) (t0 t25 t26 t27 : r1_wire.SemanticTranscript Unit)
    (cs : List (SourceFull25.Call D pre)) (init : PublicInitCall D pub pre.c1_root t0)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (initialized : r1_semantic.public_transcript D pub () pre.c1_root=ok (.Ok t0))
    (trace : SourceFull25.Trace D pre t0 t25 cs) (order : cs.map (fun c=>c.row.val)=List.range 25)
    (r25 r26 : r1_wire.ValidatedRecord) (z0 z1 : aspis_core.circle.SecureCirclePoint)
    (read25 : r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25))
    (circle25 : FinishModel.circle_validated B D t25 r25=ok (.Ok z0,t26))
    (read26 : r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26))
    (circle26 : FinishModel.circle_validated B D t26 r26=ok (.Ok z1,t27)) :
    observe (run (S1SemanticCode.verify (S1SemanticCode.finish R B) D pub bytes () none)).1=
      (initPair init::sourceLog cs) ++
      (observe (run (S1SemanticCode.circleValidated B D t25 r25)).1 ++
        observe (run (S1SemanticCode.circleValidated B D t26 r26)).1) := by
  obtain ⟨pre',t0',t25',t26',t27',cs',init',r25',r26',z0',z1',parsed',initialized',trace',order',
    read25',circle25',read26',circle26',transcript',logs⟩ := F3R_VerifyLog.log R B D pub bytes sem success
  have ep : pre'=pre := core.result.Result.Ok.inj (Result.ok.inj (parsed'.symm.trans parsed))
  subst pre'
  have e0 : t0'=t0 := core.result.Result.Ok.inj (Result.ok.inj (initialized'.symm.trans initialized))
  subst t0'
  have below : ∀ c∈cs',c.row.val<25 := by
    intro c hc
    have h : c.row.val∈cs'.map (fun c=>c.row.val) := List.mem_map.mpr ⟨c,hc,rfl⟩
    rw [order'] at h
    exact List.mem_range.mp h
  obtain ⟨e25,logEq⟩ := F3R_TraceUnique.unique trace' trace (order'.trans order.symm) below
  subst t25'
  have er25 : r25'=r25 := core.result.Result.Ok.inj (Result.ok.inj (read25'.symm.trans read25))
  subst r25'
  have e26 : t26'=t26 := congrArg Prod.snd (Result.ok.inj (circle25'.symm.trans circle25))
  subst t26'
  have er26 : r26'=r26 := core.result.Result.Ok.inj (Result.ok.inj (read26'.symm.trans read26))
  subst r26'
  rw [F3R_InitUnique.pair init' init,logEq] at logs
  exact logs

#print axioms log
end AspisR1.F3R_SemanticOnTrace
end
