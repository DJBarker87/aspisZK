import T2Nat_QuerySource
import T2Nat_ReaderFission
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ReaderPrefix
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_Try
def source (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let b4 ←
    ops.ne core.cmp.PartialEqU8
      s6 a2
  if b4
  then ok (core.result.Result.Err verifier.Error.Checkpoint)
  else
    let (state, r) ←
      ops.raw 32#usize
        { bytes, «at» := 80#usize }
    let (a3, r1) ← ops.raw 32#usize r
    let (a4, r2) ← ops.raw 32#usize r1
    let (r3, r4) ← ops.readE r2
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r5, r6) ← ops.readE r4
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let (r7, r8) ← ops.readE r6
        let cf2 ←
          core.result.Result.Insts.CoreOpsTry.branch r7
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let (r9, r10) ← ops.readE r8
          let cf3 ←
            core.result.Result.Insts.CoreOpsTry.branch r9
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let (r11, r12) ← ops.readK r10
            let cf4 ←
              core.result.Result.Insts.CoreOpsTry.branch r11
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4
              =>
              T2Nat_QuerySource.source ops bytes v i4 end1 state a3 a4
                val val1 val2 val3 val4 r12
            | core.ops.control_flow.ControlFlow.Break residual
              =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (verifier.Prepared × verifier.Accumulator)
                (core.convert.FromSame verifier.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (verifier.Prepared × verifier.Accumulator)
              (core.convert.FromSame verifier.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (verifier.Prepared × verifier.Accumulator)
            (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (verifier.Prepared × verifier.Accumulator)
          (core.convert.FromSame verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (verifier.Prepared × verifier.Accumulator)
        (core.convert.FromSame verifier.Error) residual

def normalized (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let different ← ops.ne core.cmp.PartialEqU8 s6 a2
  if different then ok (.Err .Checkpoint) else
    let (state,r1) ← ops.raw 32#usize ⟨bytes,80#usize⟩
    let (root0,r2) ← ops.raw 32#usize r1
    let (root1,r3) ← ops.raw 32#usize r2
    withRead (ops.readE r3) fun gamma r4 =>
    withRead (ops.readE r4) fun kappa r5 =>
    withRead (ops.readE r5) fun alpha0 r6 =>
    withRead (ops.readE r6) fun alpha1 r7 =>
    withRead (ops.readK r7) fun rho r8 =>
    T2Nat_QuerySource.normalized ops bytes v i4 end1 state root0 root1 gamma kappa alpha0 alpha1 rho r8

theorem source_eq (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize) :
    source ops bytes v i4 end1 s6 a2 = Port4A_NativeReader.tail ops bytes v i4 end1 s6 a2 :=
  (show source ops bytes v i4 end1 s6 a2 = T2Nat_ReaderFission.tail ops bytes v i4 end1 s6 a2 from rfl).trans
    (T2Nat_ReaderFission.source ops bytes v i4 end1 s6 a2)

theorem normalize (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize) :
    source ops bytes v i4 end1 s6 a2 = normalized ops bytes v i4 end1 s6 a2 := by
  unfold source normalized withRead
  simp only [T2Nat_QuerySource.normalize]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro different called
  cases different with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    rintro ⟨b0,r0⟩ h0
    try simp only [Aeneas.Std.uncurry]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    rintro ⟨b1,r1⟩ h1
    try simp only [Aeneas.Std.uncurry]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    rintro ⟨b2,r2⟩ h2
    try simp only [Aeneas.Std.uncurry]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    rintro ⟨value0,reader0⟩ called0
    cases value0 with
    | Err e => rfl
    | Ok x0 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      rintro ⟨value1,reader1⟩ called1
      cases value1 with
      | Err e => rfl
      | Ok x1 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
        apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        rintro ⟨value2,reader2⟩ called2
        cases value2 with
        | Err e => rfl
        | Ok x2 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
          apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
          rintro ⟨value3,reader3⟩ called3
          cases value3 with
          | Err e => rfl
          | Ok x3 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
            apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
            rintro ⟨value4,reader4⟩ called4
            cases value4 with
            | Err e => rfl
            | Ok x4 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]

#print axioms source_eq
#print axioms normalize
end AspisR1.T2Nat_ReaderPrefix
end
