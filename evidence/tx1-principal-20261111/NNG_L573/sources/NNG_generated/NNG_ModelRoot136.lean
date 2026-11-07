import NNG_LegacyCalls136
import NNG_SourceSuffixes
import NNG_TreeEmission
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelSuccess136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer)
open NMT_Transport (arr)

theorem bind_out {A B : Type} (m : Result A) (f : A → Result B) (out : B)
 (run : (do let a←m;f a)=.ok out) : ∃ a,m=.ok a ∧ f a=.ok out := by
 cases m with
 | ok a=>exact ⟨a,rfl,run⟩
 | fail e=>cases run
 | div=>cases run
#print axioms bind_out
theorem success_a3 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (r11 : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_a3 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 r11=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_a3 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) state_before_z0 (toT2 val4) (arr toT1 val5) (toT10 transcript3) (toT2 val6) r11=.ok (.Ok (toT11 out)) := by
 cases r11 with
 | Err e=>
   simp only [NNG_SourceSuffixes.f_a3,core.result.Result.unwrap,bind_tc_fail] at returned
   cases returned
 | Ok root=>
   simp only [NNG_SourceSuffixes.f_a3,core.result.Result.unwrap,bind_tc_ok] at returned
   have same := core.result.Result.Ok.inj (Result.ok.inj returned)
   subst out
   simp only [NNG_LegacySuffix136.f_a3,NNG_LegacyConfig136.boundaries,core.result.Result.unwrap,bind_tc_ok,
    NNG_LegacyConfig136.parent,NNG_Transport.toT11,NMT_Transport.arr,List.map_cons,List.map_nil]
   rfl
#print axioms success_a3
theorem success_r11 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (val7 : Slice U8)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_r11 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 val7=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_r11 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) state_before_z0 (toT2 val4) (arr toT1 val5) (toT10 transcript3) (toT2 val6) val7=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_r11 at returned
 obtain ⟨reply,copy,tail⟩ := bind_out _ _ _ returned
 unfold NNG_LegacySuffix136.f_r11
 rw [copy,bind_tc_ok]
 exact success_a3 env s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 reply out tail
#print axioms success_r11
theorem success_r10 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_r10 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_r10 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) state_before_z0 (toT2 val4) (arr toT1 val5) (toT10 transcript3) (toT2 val6)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_r10 at returned
 obtain ⟨reply,payload,tail⟩ := bind_out _ _ _ returned
 cases reply with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok bytes=>
   change NNG_SourceSuffixes.f_r11 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 bytes=.ok (.Ok out) at tail
   have old := congrArg (outer (NMP_ResultTransport.inner id toT13)) payload
   change outer (NMP_ResultTransport.inner id toT13) (NNG_Install.payload s.prefixValue 2#u8)=_ at old
   rw [NNG_Install.payload_same] at old
   simp only [outer,NMP_ResultTransport.inner,id_eq] at old
   unfold NNG_LegacySuffix136.f_r10
   dsimp only [NNG_LegacyConfig136.parent]
   rw [old,bind_tc_ok]
   exact success_r11 env s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 bytes out tail
#print axioms success_r10
end AspisR1.NNG_ModelSuccess136
