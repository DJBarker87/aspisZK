import S1CurrentPrepareCodeV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.S1PrepareCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisS1ValuesOwnedInstallation BorrowedClaimPrepared

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

private theorem semantic_source (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) :
    erase (S1SemanticCodeInstallation.code R B D pub bytes hash)=
      (NativeBuffers.install (withValues base) nativeValues R B).op9 D pub bytes hash none :=
  S1SemanticCodeInstallation.source R B D pub bytes hash

private theorem new_source (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    erase (closedPreparationCode D sem view hash scratch)=
      (NativeBuffers.install (withValues base) nativeValues R B).op8 D sem view hash scratch :=
  closedPreparationCode_erasure D sem view hash scratch

/-- Full enclosing prepare source equality, including allocation/codec/parse/
semantic rejection and outer fail/div. Both hash-bearing children are concrete
complete source code, not opaque successful child calls. Runtime/callee/SDK
association of the remaining ports is not inferred from this Result model. -/
theorem source (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    erase (prepare base R B D pub proof hash scratch)=
      verifier.candidate.prepare (NativeBuffers.install (withValues base) nativeValues R B)
        D pub proof hash none scratch := by
  unfold prepare verifier.candidate.prepare
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | apply new_source)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [semantic_source base R B] | rw [new_source base R B]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

/-- Complete returned Prepared AND gamma scratch from the SAME source tree.
The run interpreter retains the ordered digest-attempt log on outer failure. -/
theorem run_value (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    (run (prepare base R B D pub proof hash scratch)).2=
      verifier.candidate.prepare (NativeBuffers.install (withValues base) nativeValues R B)
        D pub proof hash none scratch := by
  rw [AspisR1PublicPreparation.PreparedHashCode.run_value,source]

#print axioms source
#print axioms run_value
end AspisR1CurrentCaller.S1PrepareCode
