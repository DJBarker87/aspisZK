import NGT_NBL_HashReplay
import NGT_NBA_Rho
set_option autoImplicit false
namespace AspisR1.NGT_NBL_ScalarHashReplay
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode NGT_NBL_CodeRunLaws

theorem scalar {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (nonzero : Bool)
    (s : NGT_NBL_BlockTrace.Scalar D before row payload nonzero) :
    run (PreparedScalarEffects.scalar effects NGT_NBA_Installed.actual.sampling D before row payload nonzero)=
      (NGT_NBL_HashReplay.events D before.hash s.block.log,ok (s.value,s.block.after)) := by
  have sampled := s.sample
  cases nonzero <;> simp only [Bool.false_eq_true,↓reduceIte] at sampled ⊢
  all_goals simp only [PreparedScalarEffects.scalar,bind_run,NGT_NBL_HashReplay.block D before row payload s.block,
    chain,lift_run,pure_run,sampled,lift,Bool.false_eq_true,↓reduceIte,AspisR1PublicPreparation.trace.value,Aeneas.Std.uncurry,List.append_nil,List.nil_append]

/-- Full rho effect replay on its SAME four-pass native division trace. -/
theorem rho {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (b : NGT_NBL_BlockTrace.Block D before row payload)
    (digits : List Nat) (last : List UInt32) (q : aspis_core.field.QM31)
    (trace : LPk_Induction.Digits 4 (SamplerBytePass.digits b.value) digits last)
    (packed : NGT_NBA_Rho.coordinates q=digits) :
    run (PreparedScalarEffects.scalar_k effects NGT_NBA_Installed.actual.sampling D before row payload)=
      (NGT_NBL_HashReplay.events D before.hash b.log,ok (q,b.after)) := by
  have sample := NGT_NBA_Rho.source b.value digits last q trace packed
  have fromQm : NGT_NBA_Installed.actual.sampling.fromQm q=
      ok (PreparedFromQmSourceBridge.fromQmEmbedding q) :=
    PreparedFromQmSourceBridge.fromQmSource_success q
  simp only [PreparedScalarEffects.scalar_k,bind_run,NGT_NBL_HashReplay.block D before row payload b,
    chain,lift_run,pure_run,sample,fromQm,lift,AspisR1PublicPreparation.trace.value,Aeneas.Std.uncurry,List.append_nil,List.nil_append]

#print axioms scalar
#print axioms rho
end AspisR1.NGT_NBL_ScalarHashReplay
