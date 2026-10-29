import PV_L1D_EraseControl
import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_019
import PV_L1D_Source_021
import PV_L1D_Source_023
import PV_L1D_Source_024
import PV_L1D_Source_025
import PV_L1D_Source_026
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_027
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
  Logged (core.result.Result prover.PreparedOpening verifier.Error)
  := do
  let _ ← observe .opening 0 (ok ())
  let b ← PV_L1D_Logged.lift (core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant variant
      transport.Variant.S2)
  if b
  then Pure.pure (core.result.Result.Err verifier.Error.Semantic)
  else
    let s := alloc.vec.Vec.deref backend.messages
    let coefficients ← PV_L1D_Source_025.produce variant s
    let scp ← PV_L1D_Logged.lift (Array.index_usize sem.z 1#usize)
    let we ← PV_L1D_Logged.lift (aspis_core.field.wide_exact.WideExact.from_qm31 scp.x)
    let we1 ← PV_L1D_Logged.lift (aspis_core.field.wide_exact.WideExact.from_qm31 scp.y)
    let s1 := alloc.vec.Vec.deref coefficients
    let y1 ← PV_L1D_Source_024.produce s1 { x := we, y := we1 }
    let a ← PV_L1D_Logged.lift (host_wire.SemanticTranscript.impl.state
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        sem.transcript)
    let transcript ←
      PV_L1D_Source_026.produce
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 hash a
        variant
    let s2 := alloc.vec.Vec.deref y1
    let (gamma, transcript1) ←
      PV_L1D_Source_019.produce
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        transcript 27#u8 s2 true
    let s3 := alloc.vec.Vec.deref coefficients
    let q ← PV_L1D_Source_023.produce s3 gamma
    let r ← PV_L1D_Logged.lift (weights.Weights.new variant sem.alpha sem.z)
    let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s4 := alloc.vec.Vec.deref q
      let inactive ← PV_L1D_Source_021.produce s4 val
      let a1 ← PV_L1D_Logged.lift (aspis_core.field.wide_exact.WideExact.to_le_bytes inactive)
      let s5 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice a1))
      let (kappa, transcript2) ←
        PV_L1D_Source_019.produce
          aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
          transcript1 28#u8 s5 false
      let r1 ← PV_L1D_Logged.lift (weights.Weights.materialize val kappa)
      let cf1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s6 := alloc.vec.Vec.deref q
        let s7 := alloc.vec.Vec.deref val1
        let c0 ← PV_L1D_Logged.lift (prover.round s6 s7)
        let s8 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice c0))
        let c0bytes ← PV_L1D_Logged.lift (prover.encoded_slice s8)
        let s9 := alloc.vec.Vec.deref c0bytes
        let (alpha0, transcript3) ←
          PV_L1D_Source_019.produce
            aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
            transcript2 29#u8 s9 false
        let s10 := alloc.vec.Vec.deref q
        let q1 ← PV_L1D_Logged.lift (prover.fold s10 alpha0 false)
        let s11 := alloc.vec.Vec.deref val1
        let w1 ← PV_L1D_Logged.lift (prover.fold s11 alpha0 true)
        let s12 := alloc.vec.Vec.deref q1
        let r2 ← PV_L1D_Logged.lift (host_commitment.EncodingDomain.evaluate
            aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
            backend.domain s12 0#usize)
        let r3 ← PV_L1D_Logged.lift (core.result.Result.map_err
            prover.prepare_opening.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
            r2 ())
        let cf2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          Pure.pure (core.result.Result.Ok
            {
              backend,
              sem,
              transcript := transcript3,
              y1,
              gamma,
              inactive,
              kappa,
              alpha0,
              c0bytes,
              q1,
              w1,
              folded_word := val2
            })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            prover.PreparedOpening (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.PreparedOpening (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        prover.PreparedOpening (core.convert.FromSame verifier.Error) residual

theorem complete_result
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
  erase (produce variant hash backend sem) = prover.prepare_opening variant hash backend sem := by
  unfold produce
  conv_rhs => unfold prover.prepare_opening
  simp only [PV_L1D_EraseControl.control,PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_019.complete_result,PV_L1D_Source_021.complete_result,PV_L1D_Source_023.complete_result,PV_L1D_Source_024.complete_result,PV_L1D_Source_025.complete_result,PV_L1D_Source_026.complete_result]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b called
  cases b with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true,if_false]
    iterate 11
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    cases value <;> simp only [PV_L1D_EraseControl.control,PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_019.complete_result,PV_L1D_Source_021.complete_result,PV_L1D_Source_023.complete_result,PV_L1D_Source_024.complete_result,PV_L1D_Source_025.complete_result,PV_L1D_Source_026.complete_result]
    all_goals
      repeat' first
        | split <;> simp only [PV_L1D_EraseControl.control,PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_019.complete_result,PV_L1D_Source_021.complete_result,PV_L1D_Source_023.complete_result,PV_L1D_Source_024.complete_result,PV_L1D_Source_025.complete_result,PV_L1D_Source_026.complete_result]
        | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
          intro value called
        | with_reducible rfl
#print axioms complete_result
end PV_L1D_Source_027
