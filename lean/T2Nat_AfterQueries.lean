import T2Nat_ReaderSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_AfterQueries
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_Try
def source (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (state a3 a4 : Array U8 32#usize)
    (val val1 val2 val3 : T2Nat_ReaderSuffix.E) (val4 : T2Nat_ReaderSuffix.K)
    (queries : Array U32 22#usize) (r : verifier.Reader) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let r35 ←
    ops.validate
      queries
  let cf5 ←
    core.result.Result.Insts.CoreOpsTry.branch r35
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let r36 ←
      ops.readSemanticAlpha bytes
        r.«at»
    let cf6 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r36
    match cf6 with
    | core.ops.control_flow.ControlFlow.Continue
      val5 =>
      let (semantic_alpha, at1) := val5
      T2Nat_ReaderSuffix.source ops bytes v i4 end1 state a3 a4
        val val1 val2 val3 val4 queries semantic_alpha {r with «at» := at1}
    | core.ops.control_flow.ControlFlow.Break
      residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (verifier.Prepared × verifier.Accumulator)
        (core.convert.FromSame verifier.Error)
        residual
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (verifier.Prepared × verifier.Accumulator)
      (core.convert.FromSame verifier.Error)
      residual

def normalized (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (state a3 a4 : Array U8 32#usize)
    (val val1 val2 val3 : T2Nat_ReaderSuffix.E) (val4 : T2Nat_ReaderSuffix.K)
    (queries : Array U32 22#usize) (r : verifier.Reader) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) :=
  withOk (ops.validate queries) fun _ =>
  withOk (ops.readSemanticAlpha bytes r.at) fun (semantic_alpha,at1) =>
    T2Nat_ReaderSuffix.normalized ops bytes v i4 end1 state a3 a4 val val1 val2 val3 val4
      queries semantic_alpha {r with «at» := at1}

theorem normalize (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (state a3 a4 : Array U8 32#usize)
    (val val1 val2 val3 : T2Nat_ReaderSuffix.E) (val4 : T2Nat_ReaderSuffix.K)
    (queries : Array U32 22#usize) (r : verifier.Reader) :
    source ops bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queries r =
      normalized ops bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queries r := by
  unfold source normalized withOk
  simp only [T2Nat_ReaderSuffix.normalize]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro result called
  cases result with
  | Err e => rfl
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro result returned
    cases result with
    | Err e => rfl
    | Ok pair => cases pair; rfl

#print axioms normalize
end AspisR1.T2Nat_AfterQueries
end
