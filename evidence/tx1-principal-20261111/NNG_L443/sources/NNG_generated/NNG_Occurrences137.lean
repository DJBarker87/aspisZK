import NNG_Events137
import NNG_Parse137
import NNG_ConcreteGraph136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Occurrences137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport

theorem parse (a : NNG_Data137.Args) (env : RSL.Env) (domain : RSL.TX1_137.Domain NNG_Data137.VL a) :
    RSL.Spec.map (NNG_Parse137.decode a)
      (NNG_Interpret136.call NNG_Events137.events "TX1:138/parse" (NNG_Data137.bytes a.bytes)
        (NMP_Install138.parse (NNG_Data137.bytes a.bytes))) env =
      (LIB_VParsePrefix.parsePrefix.run a.bytes) env := by
  apply NNG_EnvCallGraph136.effect_at LIB_VParsePrefix.parsePrefix a.bytes domain.2
    (NNG_Parse137.decode a) NNG_Events137.events "TX1:138/parse" (NNG_Data137.bytes a.bytes) _ env
    (LIB_Carriers.resultObs id [] (LIB_VParsePrefix.model a.bytes))
  · rw [NNG_Events137.silent env _ _ _ (by decide) (by decide) (by decide)]
    exact NNG_ConcreteGraph136.resultObs _ _ _ [] (NNG_Parse137.projected a domain)
  · exact LIB_VParsePrefix.law_exact a.bytes env
#print axioms parse

theorem publicTranscript (env : RSL.Env) (pub : LIB_VCarriers.Public) (p : LIB_VCarriers.Prefix) :
    RSL.Spec.map NNG_PublicProjection137.decode
      (NNG_Interpret136.call NNG_Events137.events "TX1:131/public_transcript"
        (fromT9 pub,(),(fromT13 (LIB_VCarriers.prefixRaw p)).c1_root)
        (NMP_Install131.publicTranscript (NNG_PublicSource137.digest env) (fromT9 pub) ()
          (fromT13 (LIB_VCarriers.prefixRaw p)).c1_root)) env =
      (LIB_VPublicTranscript.publicTranscript.run (pub,LIB_VCarriers.c1Root p)) env := by
  apply NNG_EnvCallGraph136.effect_at LIB_VPublicTranscript.publicTranscript (pub,LIB_VCarriers.c1Root p) True.intro
    NNG_PublicProjection137.decode NNG_Events137.events "TX1:131/public_transcript"
    (fromT9 pub,(),(fromT13 (LIB_VCarriers.prefixRaw p)).c1_root) _ env
    (LIB_VCode.obs env LIB_VRecords.host (AspisR1PublicPreparation.PreparedHashCode.run
      (AspisR1PublicPreparation.S1SemanticCode.publicTranscript (LIB_VCode.digest env) pub ()
        (LIB_Env.nativeKey (LIB_VCarriers.c1Root p)))))
  · rw [NNG_Events137.public_call,fromT9_inverse,NNG_PublicProjection137.root]
    have value := NNG_ConcreteGraph136.resultObs NNG_PublicProjection137.decode _ _
      (LIB_VCode.events env (AspisR1PublicPreparation.PreparedHashCode.run
        (AspisR1PublicPreparation.S1SemanticCode.publicTranscript (LIB_VCode.digest env) pub ()
          (LIB_Env.nativeKey (LIB_VCarriers.c1Root p))))).1
      (NNG_PublicProjection137.projected env pub p)
    rw [←NNG_ConcreteGraph136.mappedObs] at value
    exact value
  · exact LIB_VPublicTranscript.law_exact (pub,LIB_VCarriers.c1Root p) env
#print axioms publicTranscript

theorem begin_ (fallback : LIB_VCarriers.QM31) (env : RSL.Env) (p : LIB_VCarriers.Prefix)
    (t : LIB_VCarriers.Transcript) (borrow : p.source.val.length≤57607) :
    RSL.Spec.map (NNG_BeginProjection137.decode fallback)
      (NNG_Interpret136.call NNG_Events137.events "TX1:150/begin"
        (fromT13 (LIB_VCarriers.prefixRaw p),fromT10 t)
        (NMP_Install150.begin_ (NNG_PublicSource137.digest env) (fromT13 (LIB_VCarriers.prefixRaw p)) (fromT10 t))) env =
      (LIB_VBegin.begin_.run (p,t)) env := by
  apply NNG_EnvCallGraph136.effect_at LIB_VBegin.begin_ (p,t) borrow
    (NNG_BeginProjection137.decode fallback) NNG_Events137.events "TX1:150/begin"
    (fromT13 (LIB_VCarriers.prefixRaw p),fromT10 t) _ env
    (LIB_Carriers.resultObs id (LIB_VBegin.events (p,t) env) (LIB_VBegin.model (p,t) env))
  · rw [NNG_Events137.begin_call,fromT13_inverse,fromT10_inverse,←LIB_VBegin.effects_exact (p,t) env]
    exact NNG_ConcreteGraph136.resultObs _ _ _ _ (NNG_BeginProjection137.projected fallback env p t)
  · exact LIB_VBegin.law_exact (p,t) env
#print axioms begin_
end AspisR1.NNG_Occurrences137
