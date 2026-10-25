import F3J_OpeningCode
import S1PreparedScalarEffectsV1
import AuS1_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_ScalarCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode

theorem scalar {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedModel.Boundaries)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (value : Array U8 32#usize) (nonzero : Bool)
    (success : transcript.Transcript.block D before row payload=ok (value,after)) :
    observe (run (PreparedScalarEffects.scalar effects B D before row payload nonzero)).1=
      observe (run (PreparedHashEffects.block effects D before row payload)).1 := by
  unfold PreparedScalarEffects.scalar
  change observe (run (PreparedHashCode.bind (PreparedHashEffects.block effects D before row payload) _)).1=_
  rw [AuS1_Trace.run_bind,run_value,block_erasure,success]
  simp only [AuS1_Trace.continueRun,AuS1_Trace.observe_append]
  have empty : (run (do
      let out ← (if nonzero then B.gamma value else B.ordinary value)
      let i ← lift (UScalar.cast .Usize row)
      trace.value 4#u16 i out
      pure (out,after) : Code _)).1=[] := by
    cases nonzero <;>
      simp only [Bool.false_eq_true,if_false,if_true,Bind.bind,Pure.pure,
        PreparedHashCode.bind,liftM,MonadLift.monadLift,MonadLiftT.monadLift]
    · cases B.ordinary value <;> rfl
    · cases B.gamma value <;> rfl
  rw [empty]
  rfl

theorem rho {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedModel.Boundaries)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (value : Array U8 32#usize)
    (success : transcript.Transcript.block D before row payload=ok (value,after)) :
    observe (run (PreparedScalarEffects.scalar_k effects B D before row payload)).1=
      observe (run (PreparedHashEffects.block effects D before row payload)).1 := by
  unfold PreparedScalarEffects.scalar_k
  change observe (run (PreparedHashCode.bind (PreparedHashEffects.block effects D before row payload) _)).1=_
  rw [AuS1_Trace.run_bind,run_value,block_erasure,success]
  simp only [AuS1_Trace.continueRun,AuS1_Trace.observe_append]
  have empty : (run (do
      let out ← sampler.qm31_sample value
      let i ← lift (UScalar.cast .Usize row)
      let wide ← B.fromQm out
      trace.value 4#u16 i wide
      pure (out,after) : Code _)).1=[] := by
    simp only [Bind.bind,Pure.pure,PreparedHashCode.bind,liftM,MonadLift.monadLift,MonadLiftT.monadLift]
    cases h : sampler.qm31_sample value with
    | fail e => rfl
    | div => rfl
    | ok q => cases B.fromQm q <;> rfl
  rw [empty]
  rfl

#print axioms scalar
#print axioms rho
end AspisR1.F3J_ScalarCode
end
