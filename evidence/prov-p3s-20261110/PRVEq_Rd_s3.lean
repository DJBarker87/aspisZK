-- PCVU_ item (2): the frozen 4bb3b3f read_checkpoint_semantic_alpha / read_checkpoint_weights (emission PCVU_E002, overflow ON, text with the QM31::from_le_bytes
-- external and the Vec into_iter_mut external as parameters) against the deployed reader ops, stated as the Leaves sem/weights shape.
import Aeneas
import PRVEq_QM31_s3
import PRVEq_Tx2Deployed_s1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
noncomputable section
namespace PCVU_Rd
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1 PCVQ_Resumeq13
namespace PCVU_Fresh2
/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::Reader<'a>}::raw]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 344:4-344:116 -/
def verifier.Reader.raw
  (N : Std.Usize) (self : verifier.Reader) :
  Result ((Array Std.U8 N) × verifier.Reader)
  := do
  let i ← self.«at» + N
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) self.bytes { start := self.«at», «end» := i }
  let r ← core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 s
  let b ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  ok (b, { self with «at» := i })

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::Reader<'a>}::k]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 347:4-347:98 -/
def verifier.Reader.k
  (fle : Slice Std.U8 → Result (Option aspis_core.field.QM31))
  (self : verifier.Reader) :
  Result ((core.result.Result aspis_core.field.QM31 verifier.Error) ×
    verifier.Reader)
  := do
  let (a, self1) ← verifier.Reader.raw 16#usize self
  let s ← lift (Array.to_slice a)
  let o ← fle s
  let r ← core.option.Option.ok_or o AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint
  ok (r, self1)

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 364:4-371:1 -/
@[rust_loop_body]
def verifier.read_checkpoint_weights_loop.body
  (fle : Slice Std.U8 → Result (Option aspis_core.field.QM31)) (bytes : Slice Std.U8) (iter : core.slice.iter.IterMut aspis_core.field.QM31)
  (back : core.slice.iter.IterMut aspis_core.field.QM31 →
  core.slice.iter.IterMut aspis_core.field.QM31) (at1 : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.IterMut aspis_core.field.QM31) ×
    (core.slice.iter.IterMut aspis_core.field.QM31 → core.slice.iter.IterMut
    aspis_core.field.QM31) × Std.Usize) (Std.Usize × (Option
    (core.result.Result ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
    verifier.Error)) × (core.slice.iter.IterMut aspis_core.field.QM31)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => let im := next_back iter1 none
            ok (done (at1, none, back im))
  | some _ =>
    let (r, reader) ← verifier.Reader.k fle { bytes, «at» := at1 }
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      ok (cont (iter1, fun im => let im1 := next_back im (some val)
                                 back im1, reader.«at»))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
          (core.convert.FromSame verifier.Error) residual
      let im := next_back iter1 o
      ok (done (at1, some r1, back im))

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 364:4-371:1 -/
@[rust_loop]
def verifier.read_checkpoint_weights_loop
  (fle : Slice Std.U8 → Result (Option aspis_core.field.QM31)) (iter : core.slice.iter.IterMut aspis_core.field.QM31)
  (back : core.slice.iter.IterMut aspis_core.field.QM31 →
  core.slice.iter.IterMut aspis_core.field.QM31) (bytes : Slice Std.U8)
  (at1 : Std.Usize) :
  Result (Std.Usize × (Option (core.result.Result ((alloc.vec.Vec
    aspis_core.field.QM31) × Std.Usize) verifier.Error)) ×
    (core.slice.iter.IterMut aspis_core.field.QM31))
  := do
  loop
    (fun (iter1, back1, at2) => verifier.read_checkpoint_weights_loop.body
      fle bytes iter1 back1 at2)
    (iter, back, at1)

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 363:0-371:1 -/
def verifier.read_checkpoint_weights
  (fle : Slice Std.U8 → Result (Option aspis_core.field.QM31)) (into_iter : alloc.vec.Vec aspis_core.field.QM31 → Result ((core.slice.iter.IterMut aspis_core.field.QM31) × (core.slice.iter.IterMut aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31))) (bytes : Slice Std.U8) (at1 : Std.Usize)
  (weights : alloc.vec.Vec aspis_core.field.QM31) :
  Result (core.result.Result ((alloc.vec.Vec aspis_core.field.QM31) ×
    Std.Usize) verifier.Error)
  := do
  let (iter, into_iter_back) ←
    into_iter weights
  let (at2, pending_return, back) ←
    verifier.read_checkpoint_weights_loop fle iter (fun im => im) bytes at1
  match pending_return with
  | none =>
    let weights1 := into_iter_back back
    ok (core.result.Result.Ok (weights1, at2))
  | some r => ok r

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_semantic_alpha]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 375:0-390:1 -/
def verifier.read_checkpoint_semantic_alpha
  (fle : Slice Std.U8 → Result (Option aspis_core.field.QM31)) (bytes : Slice Std.U8) (at1 : Std.Usize) :
  Result (core.result.Result ((Array aspis_core.field.QM31 10#usize) ×
    Std.Usize) verifier.Error)
  := do
  let (r, r1) ← verifier.Reader.k fle { bytes, «at» := at1 }
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r2, r3) ← verifier.Reader.k fle r1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let (r4, r5) ← verifier.Reader.k fle r3
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let (r6, r7) ← verifier.Reader.k fle r5
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let (r8, r9) ← verifier.Reader.k fle r7
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r8
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let (r10, r11) ← verifier.Reader.k fle r9
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r10
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let (r12, r13) ← verifier.Reader.k fle r11
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r12
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val6 =>
                let (r14, r15) ← verifier.Reader.k fle r13
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r14
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val7 =>
                  let (r16, r17) ← verifier.Reader.k fle r15
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r16
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue val8 =>
                    let (r18, r19) ← verifier.Reader.k fle r17
                    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r18
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val9 =>
                      ok (core.result.Result.Ok
                        (Array.make 10#usize [
                           val, val1, val2, val3, val4, val5, val6, val7, val8,
                           val9
                           ], r19.«at»))
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
                        (core.convert.FromSame verifier.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
                      (core.convert.FromSame verifier.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
                    (core.convert.FromSame verifier.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
                  (core.convert.FromSame verifier.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
                (core.convert.FromSame verifier.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
              (core.convert.FromSame verifier.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
            (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
          (core.convert.FromSame verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
        (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
      (core.convert.FromSame verifier.Error) residual

end PCVU_Fresh2

abbrev fle0 := PCVU_QM31.PCVU_Fresh.field.QM31.from_le_bytes

theorem frk {B : Type} (r : verifier.Reader)
    (K : core.result.Result aspis_core.field.QM31 VErr × verifier.Reader → Result B) :
    (PCVU_Fresh2.verifier.Reader.k fle0 r >>= K) =
      (CheckpointBytes3Reader.readK r >>= fun p => K (phi p.1, p.2)) := by
  unfold PCVU_Fresh2.verifier.Reader.k CheckpointBytes3Reader.readK
  have hraw : PCVU_Fresh2.verifier.Reader.raw 16#usize r = CheckpointBytes3Reader.raw 16#usize r := rfl
  rw [hraw]
  simp only [bind_assoc, bind_tc_ok, lift]
  congr 1; funext p
  rcases p with ⟨b, out⟩
  have w : b.to_slice.val.length = 16 := by simpa [Array.to_slice] using b.property
  have e := PCVU_QM31.qm31_16 b.to_slice w
  simp only [fle0, e, bind_assoc, bind_tc_ok]
  congr 1; funext q
  cases q <;> rfl

theorem step {T : Type} (r : verifier.Reader)
    (cont : aspis_core.field.QM31 → verifier.Reader → Result (core.result.Result T VErr))
    (next : aspis_core.field.QM31 → verifier.Reader → Result (core.result.Result T SErr))
    (h : ∀ x r', cont x r' = (next x r' >>= fun o => ok (phi o))) :
    (PCVU_Fresh2.verifier.Reader.k fle0 r >>= fun (rr, r1) => (do
        let cf ← core.result.Result.Insts.CoreOpsTry.branch rr
        match cf with
        | core.ops.control_flow.ControlFlow.Continue v => cont v r1
        | core.ops.control_flow.ControlFlow.Break res =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual T
              (core.convert.FromSame VErr) res)) =
    (CheckpointBytes4Ops.withK CheckpointBytes3Reader.readK r next >>= fun o => ok (phi o)) := by
  rw [frk]
  unfold CheckpointBytes4Ops.withK
  simp only [bind_assoc, bind_tc_ok]
  congr 1; funext p
  rcases p with ⟨v, out⟩
  cases v with
  | Err e =>
    simp [phi, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame]
  | Ok x =>
    simp [phi, core.result.Result.Insts.CoreOpsTry.branch, h]

theorem sem_eq (bytes : Slice Std.U8) (at1 : Std.Usize) :
    PCVU_Fresh2.verifier.read_checkpoint_semantic_alpha fle0 bytes at1 =
      (CheckpointBytes4Ops.readSemanticAlpha bytes at1 >>= fun r => ok (phi r)) := by
  unfold PCVU_Fresh2.verifier.read_checkpoint_semantic_alpha CheckpointBytes4Ops.readSemanticAlpha
    CheckpointBytes4Ops.semanticUsing
  apply step; intro x0 r1
  apply step; intro x1 r2
  apply step; intro x2 r3
  apply step; intro x3 r4
  apply step; intro x4 r5
  apply step; intro x5 r6
  apply step; intro x6 r7
  apply step; intro x7 r8
  apply step; intro x8 r9
  apply step; intro x9 r10
  first | rfl | simp [phi]

#print axioms frk
#print axioms step
#print axioms sem_eq
end PCVU_Rd
