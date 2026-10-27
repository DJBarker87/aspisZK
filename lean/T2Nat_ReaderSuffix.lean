import T2Nat_QueryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ReaderSuffix
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_Try
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev K := aspis_core.field.QM31

def source (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (state a3 a4 : Array U8 32#usize)
    (val val1 val2 val3 : E) (val4 : K) (queries : Array U32 22#usize)
    (semantic_alpha : Array K 10#usize) (r : verifier.Reader) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let (r37, r38) ←
    ops.readK
      r
  let cf7 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r37
  match cf7 with
  | core.ops.control_flow.ControlFlow.Continue
    val6 =>
    let (r39, r40) ← ops.readK r38
    let cf8 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r39
    match cf8 with
    |
      core.ops.control_flow.ControlFlow.Continue
      val7 =>
      let (r41, r42) ← ops.readK r40
      let cf9 ←
        core.result.Result.Insts.CoreOpsTry.branch
          r41
      match cf9 with
      |
        core.ops.control_flow.ControlFlow.Continue
        val8 =>
        let (r43, r44) ←
          ops.readK r42
        let cf10 ←
          core.result.Result.Insts.CoreOpsTry.branch
            r43
        match cf10 with
        |
          core.ops.control_flow.ControlFlow.Continue
          val9 =>
          let (r45, r46) ←
            ops.readE r44
          let cf11 ←
            core.result.Result.Insts.CoreOpsTry.branch
              r45
          match cf11 with
          |
            core.ops.control_flow.ControlFlow.Continue
            val10 =>
            let (r47, r48) ←
              ops.readE r46
            let cf12 ←
              core.result.Result.Insts.CoreOpsTry.branch
                r47
            match cf12 with
            |
              core.ops.control_flow.ControlFlow.Continue
              val11 =>
              let (r49, r50) ←
                ops.readK r48
              let cf13 ←
                core.result.Result.Insts.CoreOpsTry.branch
                  r49
              match cf13 with
              |
                core.ops.control_flow.ControlFlow.Continue
                val12 =>
                let i30 ←
                  ops.finalLen v
                let q ←
                  ops.zeroK
                let r52 ← ops.filled i30 q
                let cf14 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r52
                match cf14 with
                |
                  core.ops.control_flow.ControlFlow.Continue
                  val13 =>
                  let r53 ←
                    ops.readWeights
                      bytes r50.«at» val13
                  let cf15 ←
                    core.result.Result.Insts.CoreOpsTry.branch
                      r53
                  match cf15 with
                  |
                    core.ops.control_flow.ControlFlow.Continue
                    val14 =>
                    let (weights, at2) := val14
                    if at2 != end1
                    then
                      ok
                        (core.result.Result.Err
                        verifier.Error.Checkpoint)
                    else
                      let i31 ←
                        lift (UScalar.cast
                          .Usize i4)
                      ok (core.result.Result.Ok
                        ({
                           variant := v,
                           roots :=
                             (Array.make
                                2#usize [
                               a3, a4
                               ]),
                           gamma := val,
                           kappa := val1,
                           alpha :=
                             (Array.make
                                2#usize [
                               val2, val3
                               ]),
                           rho := val4,
                           queries :=
                             queries,
                           semantic_alpha,
                           z :=
                             (Array.make
                                2#usize [
                               {
                                 x := val6,
                                 y := val7
                               },
                               {
                                 x := val8,
                                 y := val9
                               }
                               ]),
                           claim := val10,
                           state
                         },
                        {
                          weights,
                          rhs := val11,
                          power := val12,
                          next := i31
                        }))
                  |
                    core.ops.control_flow.ControlFlow.Break
                    residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (verifier.Prepared ×
                      verifier.Accumulator)
                      (core.convert.FromSame
                      verifier.Error) residual
                |
                  core.ops.control_flow.ControlFlow.Break
                  residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (verifier.Prepared ×
                    verifier.Accumulator)
                    (core.convert.FromSame
                    verifier.Error) residual
              |
                core.ops.control_flow.ControlFlow.Break
                residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (verifier.Prepared ×
                  verifier.Accumulator)
                  (core.convert.FromSame
                  verifier.Error) residual
            |
              core.ops.control_flow.ControlFlow.Break
              residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (verifier.Prepared ×
                verifier.Accumulator)
                (core.convert.FromSame
                verifier.Error) residual
          |
            core.ops.control_flow.ControlFlow.Break
            residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (verifier.Prepared ×
              verifier.Accumulator)
              (core.convert.FromSame
              verifier.Error) residual
        |
          core.ops.control_flow.ControlFlow.Break
          residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (verifier.Prepared ×
            verifier.Accumulator)
            (core.convert.FromSame
            verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break
        residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (verifier.Prepared ×
          verifier.Accumulator)
          (core.convert.FromSame
          verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break
      residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (verifier.Prepared ×
        verifier.Accumulator)
        (core.convert.FromSame verifier.Error)
        residual
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (verifier.Prepared ×
      verifier.Accumulator)
      (core.convert.FromSame verifier.Error)
      residual

def normalized (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (state a3 a4 : Array U8 32#usize)
    (val val1 val2 val3 : E) (val4 : K) (queries : Array U32 22#usize)
    (semantic_alpha : Array K 10#usize) (r : verifier.Reader) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) :=
    withRead (ops.readK r) fun zx0 r10 =>
    withRead (ops.readK r10) fun zy0 r11 =>
    withRead (ops.readK r11) fun zx1 r12 =>
    withRead (ops.readK r12) fun zy1 r13 =>
    withRead (ops.readE r13) fun claim r14 =>
    withRead (ops.readE r14) fun rhs r15 =>
    withRead (ops.readK r15) fun power r16 => do
    let width ← ops.finalLen v
    let zero ← ops.zeroK
    withOk (ops.filled width zero) fun initial =>
    withOk (ops.readWeights bytes r16.at initial) fun (weights,at2) => do
    if at2 != end1 then ok (.Err .Checkpoint) else
      let cursor ← lift (UScalar.cast .Usize i4)
      ok (.Ok (⟨v,Array.make 2#usize [a3,a4],val,val1,
        Array.make 2#usize [val2,val3],val4,queries,semantic_alpha,
        Array.make 2#usize [⟨zx0,zy0⟩,⟨zx1,zy1⟩],claim,state⟩,
        ⟨weights,rhs,power,cursor⟩))

theorem normalize (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (state a3 a4 : Array U8 32#usize)
    (val val1 val2 val3 : E) (val4 : K) (queries : Array U32 22#usize)
    (semantic_alpha : Array K 10#usize) (r : verifier.Reader) :
    source ops bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha r =
      normalized ops bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha r := by
  unfold source normalized withRead withOk
  repeat
    first
    | rfl
    | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro x hx; try rcases x with ⟨a,b⟩)
    | (simp only [bind_tc_ok,Aeneas.Std.uncurry])
    | (split <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,Aeneas.Std.uncurry])

#print axioms normalize
end AspisR1.T2Nat_ReaderSuffix
end
