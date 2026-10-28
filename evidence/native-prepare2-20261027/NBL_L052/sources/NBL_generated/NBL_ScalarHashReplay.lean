import NBL_HashReplay
import NBA_Rho
set_option autoImplicit false
namespace AspisR1.NBL_ScalarHashReplay
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode NBL_CodeRunLaws

theorem scalar {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (nonzero : Bool)
    (s : NBL_BlockTrace.Scalar D before row payload nonzero) :
    run (PreparedScalarEffects.scalar effects NBA_Installed.actual.sampling D before row payload nonzero)=
      (NBL_HashReplay.events D before.hash s.block.log,ok (s.value,s.block.after)) := by
  have sampled := s.sample
  cases nonzero <;> simp only [Bool.false_eq_true,↓reduceIte] at sampled ⊢
  all_goals simp only [PreparedScalarEffects.scalar,bind_run,NBL_HashReplay.block D before row payload s.block,
    chain,lift_run,pure_run,sampled,lift,AspisR1PublicPreparation.trace.value,Aeneas.Std.uncurry,List.append_nil,List.nil_append]

/-- Full rho effect replay on its SAME four-pass native division trace. -/
theorem rho {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (b : NBL_BlockTrace.Block D before row payload)
    (digits : List Nat) (last : List UInt32) (q : aspis_core.field.QM31)
    (trace : LPk_Induction.Digits 4 (SamplerBytePass.digits b.value) digits last)
    (packed : NBA_Rho.coordinates q=digits) :
    run (PreparedScalarEffects.scalar_k effects NBA_Installed.actual.sampling D before row payload)=
      (NBL_HashReplay.events D before.hash b.log,ok (q,b.after)) := by
  have sample := NBA_Rho.source b.value digits last q trace packed
  have fromQm : NBA_Installed.actual.sampling.fromQm q=
      ok (PreparedFromQmSourceBridge.fromQmEmbedding q) :=
    PreparedFromQmSourceBridge.fromQmSource_success q
  simp only [PreparedScalarEffects.scalar_k,bind_run,NBL_HashReplay.block D before row payload b,
    chain,lift_run,pure_run,sample,fromQm,lift,AspisR1PublicPreparation.trace.value,Aeneas.Std.uncurry,List.append_nil,List.nil_append]

#print axioms scalar
#print axioms rho
end AspisR1.NBL_ScalarHashReplay
