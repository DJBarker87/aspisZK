import NDO_JHa_PreparedGamma
import RPt_JFr_TX2_Powers
import NDO_JGr_Geometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Powers
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition AspisR1ClaimPreparedBridge

theorem transport :
    (do let rs ← powersPublic 29#usize JHa_GammaSample.value
        ok (Tx1Q_Carriers.arr Tx1Q_Carriers.e (mapArray currentE rs))) =
      Tx2N_Powers.powers 29#usize JFo_Prepared.value.gamma := by
  unfold powersPublic AspisR1CurrentPreparedClaim.ClaimPowers.powers Tx2N_Powers.powers
  have input : AspisR1CurrentPreparedClaim.ClaimPowers.toPowers (toClaimE JHa_GammaSample.value)=
      Tx2N_Powers.toPowers JFo_Prepared.value.gamma := rfl
  rw [input]
  cases call : AspisR1LoopPowers.weights.early_powers 29#usize
    (Tx2N_Powers.toPowers JFo_Prepared.value.gamma) with
  | fail e => rfl
  | div => rfl
  | ok out =>
    simp only [bind_tc_ok]
    congr 1
    apply Subtype.ext
    simp only [Tx1Q_Carriers.arr,mapArray,AspisR1CurrentPreparedClaim.ClaimPowers.mapArray,
      Tx2N_Powers.mapArray,List.map_map]
    rfl
#print axioms transport

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare JGr_Geometry.installed JGr_Geometry.digest
      (toCurrentPublic JFs_PublicSerialization.value) JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    p.gamma=currentE JHa_GammaSample.value ∧
      Tx1Q_Carriers.arr Tx1Q_Carriers.e scratch=JFr_TX2_Powers.value := by
  obtain ⟨gamma,rs,call,same⟩ := JHa_PreparedGamma.source _ _ _ JGn_TerminalIdentified.shaDictionary
    () p input scratch prepare
  refine ⟨gamma,?_⟩
  have eq := transport
  rw [call,bind_tc_ok,same,JFr_TX2_Powers.source] at eq
  exact Result.ok.inj eq
#print axioms source
end AspisR1.JHa_Powers
end
