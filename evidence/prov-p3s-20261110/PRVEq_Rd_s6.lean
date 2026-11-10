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
  change ((do
      let o ← PCVU_QM31.PCVU_Fresh.field.QM31.from_le_bytes b.to_slice
      let r ← core.option.Option.ok_or o AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint
      ok (r, out)) >>= K) = ((do
      let q ← OraclePortCkptAbi2Extracted.decode_k_spec b.to_slice
      ok (CheckpointBytes3Reader.optionK q, out)) >>= fun p => K (phi p.1, p.2))
  rw [e]
  simp only [bind_assoc, bind_tc_ok]
  congr 1; funext q
  cases q <;> rfl

def stepF {T : Type} (r : verifier.Reader)
    (cont : aspis_core.field.QM31 → verifier.Reader → Result (core.result.Result T VErr)) :
    Result (core.result.Result T VErr) :=
  PCVU_Fresh2.verifier.Reader.k fle0 r >>= fun (rr, r1) => (do
    let cf ← core.result.Result.Insts.CoreOpsTry.branch rr
    match cf with
    | core.ops.control_flow.ControlFlow.Continue v => cont v r1
    | core.ops.control_flow.ControlFlow.Break res =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual T
          (core.convert.FromSame VErr) res)

theorem step {T : Type} (r : verifier.Reader)
    (cont : aspis_core.field.QM31 → verifier.Reader → Result (core.result.Result T VErr))
    (next : aspis_core.field.QM31 → verifier.Reader → Result (core.result.Result T SErr))
    (h : ∀ x r', cont x r' = (next x r' >>= fun o => ok (phi o))) :
    stepF r cont =
    (CheckpointBytes4Ops.withK CheckpointBytes3Reader.readK r next >>= fun o => ok (phi o)) := by
  unfold stepF
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

def semS (bytes : Slice Std.U8) (at1 : Std.Usize) : Result (core.result.Result ((Std.Array aspis_core.field.QM31 10#usize) × Std.Usize) VErr) :=
  stepF ⟨bytes, at1⟩ (fun v0 s1 => stepF s1 (fun v1 s2 => stepF s2 (fun v2 s3 => stepF s3 (fun v3 s4 => stepF s4 (fun v4 s5 => stepF s5 (fun v5 s6 => stepF s6 (fun v6 s7 => stepF s7 (fun v7 s8 => stepF s8 (fun v8 s9 => stepF s9 (fun v9 s10 => ok (core.result.Result.Ok (Array.make 10#usize [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9], s10.«at»))))))))))))

theorem sem_text (bytes : Slice Std.U8) (at1 : Std.Usize) :
    PCVU_Fresh2.verifier.read_checkpoint_semantic_alpha fle0 bytes at1 = semS bytes at1 := rfl

theorem sem_eq (bytes : Slice Std.U8) (at1 : Std.Usize) :
    PCVU_Fresh2.verifier.read_checkpoint_semantic_alpha fle0 bytes at1 =
      (CheckpointBytes4Ops.readSemanticAlpha bytes at1 >>= fun r => ok (phi r)) := by
  rw [sem_text]
  unfold semS CheckpointBytes4Ops.readSemanticAlpha CheckpointBytes4Ops.semanticUsing
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
#print axioms sem_text
#print axioms sem_eq

-- ===== weights: frozen mutable-iterator loop (deferred writebacks) against the deployed write-through weightLoop =====
abbrev KK := aspis_core.field.QM31

def bs {α β : Type} (body : α → Result (ControlFlow α β)) (h : α → Result β) (x : α) : Result β :=
  match body x with
  | ok r => match r with
    | ControlFlow.cont x' => h x'
    | ControlFlow.done y => ok y
  | fail e => fail e
  | div => div

theorem loop_unfold {α β : Type} (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = bs body (loop body) x := by
  rw [loop]; rfl

/-- Writes in the frozen (outermost-first) order. -/
def owS (s : Slice KK) (q : Nat) : List KK → Slice KK
  | [] => s
  | y :: ys => Slice.setAtNat (owS s (q + 1) ys) q y
/-- Writes in the deployed (write-through, innermost-first) order. -/
def dwS (s : Slice KK) (q : Nat) : List KK → Slice KK
  | [] => s
  | y :: ys => dwS (Slice.setAtNat s q y) (q + 1) ys

theorem setAtNat_val (s : Slice KK) (i : Nat) (x : KK) : (Slice.setAtNat s i x).val = s.val.set i x := rfl

theorem setAtNat_comm (s : Slice KK) (p q : Nat) (x y : KK) (h : p ≠ q) :
    Slice.setAtNat (Slice.setAtNat s p x) q y = Slice.setAtNat (Slice.setAtNat s q y) p x := by
  apply Subtype.ext
  simp only [setAtNat_val]
  exact List.set_comm x y h

theorem ow_set_comm (s : Slice KK) (p : Nat) (x : KK) (ws : List KK) :
    ∀ (q : Nat), p < q → owS (Slice.setAtNat s p x) q ws = Slice.setAtNat (owS s q ws) p x := by
  induction ws with
  | nil => intro q _; rfl
  | cons y ys ih =>
    intro q hq
    simp only [owS]
    rw [ih (q + 1) (by omega)]
    exact setAtNat_comm _ _ _ _ _ (by omega)

theorem dw_eq_ow (ws : List KK) : ∀ (s : Slice KK) (q : Nat), dwS s q ws = owS s q ws := by
  induction ws with
  | nil => intro s q; rfl
  | cons y ys ih =>
    intro s q
    simp only [dwS, owS]
    rw [ih, ow_set_comm _ _ _ _ _ (by omega)]

theorem ow_snoc (s : Slice KK) (x : KK) (ws : List KK) :
    ∀ (q : Nat), owS s q (ws ++ [x]) = owS (Slice.setAtNat s (q + ws.length) x) q ws := by
  induction ws generalizing s with
  | nil => intro q; rfl
  | cons y ys ih =>
    intro q
    simp only [List.cons_append, owS, List.length_cons]
    rw [ih s (q + 1)]
    have : q + 1 + ys.length = q + (ys.length + 1) := by omega
    rw [this]

theorem dw_snoc (x : KK) (ws : List KK) :
    ∀ (s : Slice KK) (q : Nat), dwS s q (ws ++ [x]) = Slice.setAtNat (dwS s q ws) (q + ws.length) x := by
  induction ws with
  | nil => intro s q; rfl
  | cons y ys ih =>
    intro s q
    simp only [List.cons_append, dwS, List.length_cons]
    rw [ih]
    have : q + 1 + ys.length = q + (ys.length + 1) := by omega
    rw [this]

theorem bs_bind {α β : Type} (body : α → Result (ControlFlow α β)) (h : α → Result β) (x : α) :
    bs body h x = (body x >>= fun cf => match cf with | ControlFlow.cont x' => h x' | ControlFlow.done y => ok y) := by
  unfold bs
  cases hb : body x with
  | ok r => cases r <;> rfl
  | fail e => rfl
  | div => rfl

def convW (res : core.result.Result (core.slice.iter.IterMut KK × verifier.Reader) SErr) :
    core.result.Result (alloc.vec.Vec KK × Std.Usize) VErr :=
  match res with
  | .Err e => .Err (Port3_CheckpointInstall.error e)
  | .Ok (it, r) => .Ok (⟨it.slice.val, it.slice.property⟩, r.«at»)

def post (res : Std.Usize × (Option (core.result.Result (alloc.vec.Vec KK × Std.Usize) VErr)) × (core.slice.iter.IterMut KK)) :
    core.result.Result (alloc.vec.Vec KK × Std.Usize) VErr :=
  match res with
  | (at2, none, im) => .Ok (⟨im.slice.val, im.slice.property⟩, at2)
  | (_, some r, _) => r

theorem dw_length (ws : List KK) : ∀ (s : Slice KK) (q : Nat), (dwS s q ws).val.length = s.val.length := by
  induction ws with
  | nil => intro s q; rfl
  | cons y ys ih =>
    intro s q
    simp only [dwS]
    rw [ih]
    exact Slice.setAtNat_length s q y

theorem readK_bytes (r : verifier.Reader) (v : core.result.Result KK SErr) (out : verifier.Reader)
    (h : CheckpointBytes3Reader.readK r = ok (v, out)) : out.bytes = r.bytes := by
  unfold CheckpointBytes3Reader.readK at h
  obtain ⟨⟨b, o0⟩, hraw, t1⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨q, _, t2⟩ := OraclePortCkptAbiTry.bind_success _ _ _ t1
  have e2 := Result.ok.inj t2
  have eo : o0 = out := (Prod.mk.inj e2).2
  subst eo
  unfold CheckpointBytes3Reader.raw AspisR1Stage2.verifier.Reader.rawWithUnwrap at hraw
  obtain ⟨i, _, t3⟩ := OraclePortCkptAbiTry.bind_success _ _ _ hraw
  obtain ⟨s, _, t4⟩ := OraclePortCkptAbiTry.bind_success _ _ _ t3
  obtain ⟨a, _, t5⟩ := OraclePortCkptAbiTry.bind_success _ _ _ t4
  obtain ⟨b', _, t6⟩ := OraclePortCkptAbiTry.bind_success _ _ _ t5
  have e6 := Result.ok.inj t6
  have eo2 : ({ r with «at» := i } : verifier.Reader) = o0 := (Prod.mk.inj e6).2
  rw [← eo2]

theorem next_some (S : Slice KK) (i : Nat) (h : i < S.val.length) :
    ∃ x : KK, core.slice.iter.IteratorIterMut.next (⟨S, i⟩ : core.slice.iter.IterMut KK) =
      ok (some x, (⟨S, i + 1⟩ : core.slice.iter.IterMut KK),
        fun it' x => match x with | none => it' | some x => {it' with slice := it'.slice.setAtNat i x}) := by
  have h' : i < (S.len : Std.Usize).val := by rw [Slice.len_val]; simpa [Slice.length] using h
  refine ⟨_, ?_⟩
  simp only [core.slice.iter.IteratorIterMut.next]
  rw [dif_pos h']

theorem next_none (S : Slice KK) (i : Nat) (h : ¬ i < S.val.length) :
    core.slice.iter.IteratorIterMut.next (⟨S, i⟩ : core.slice.iter.IterMut KK) =
      ok (none, (⟨S, i⟩ : core.slice.iter.IterMut KK), fun it _ => it) := by
  have h' : ¬ i < (S.len : Std.Usize).val := by rw [Slice.len_val]; simpa [Slice.length] using h
  simp only [core.slice.iter.IteratorIterMut.next]
  rw [dif_neg h']

theorem loop_claim : ∀ (n : Nat) (r : verifier.Reader) (S : Slice KK) (q : Nat) (ws : List KK),
    q + ws.length + n = S.val.length →
    (PCVU_Fresh2.verifier.read_checkpoint_weights_loop fle0 ⟨S, q + ws.length⟩
        (fun im => {im with slice := owS im.slice q ws}) r.bytes r.«at» >>= fun res => ok (post res)) =
    (CheckpointBytes4Sections.weightLoop CheckpointBytes3Reader.readK n r ⟨dwS S q ws, q + ws.length⟩
        >>= fun res => ok (convW res)) := by
  intro n
  induction n with
  | zero =>
    intro r S q ws h
    have hn : ¬ (q + ws.length < S.val.length) := by omega
    unfold PCVU_Fresh2.verifier.read_checkpoint_weights_loop
    rw [loop_unfold, bs_bind]
    unfold PCVU_Fresh2.verifier.read_checkpoint_weights_loop.body
    try dsimp only
    rw [next_none S _ hn]
    simp [CheckpointBytes4Sections.weightLoop, post, convW, dw_eq_ow]
  | succ n ih =>
    intro r S q ws h
    have hlt : q + ws.length < S.val.length := by omega
    have hlt' : q + ws.length < (dwS S q ws).val.length := by rw [dw_length]; exact hlt
    unfold PCVU_Fresh2.verifier.read_checkpoint_weights_loop
    rw [loop_unfold, bs_bind]
    unfold PCVU_Fresh2.verifier.read_checkpoint_weights_loop.body
    try dsimp only
    obtain ⟨x0, hn0⟩ := next_some S _ hlt
    obtain ⟨x1, hn1⟩ := next_some (dwS S q ws) _ hlt'
    rw [hn0]
    simp only [CheckpointBytes4Sections.weightLoop]
    rw [hn1]
    have eta : ({ bytes := r.bytes, «at» := r.«at» } : verifier.Reader) = r := rfl
    simp only [bind_assoc, bind_tc_ok, eta]
    rw [frk]
    cases hk : CheckpointBytes3Reader.readK r with
    | fail e => simp
    | div => simp
    | ok p =>
      rcases p with ⟨v, out⟩
      have hb := readK_bytes r v out hk
      simp only [bind_tc_ok]
      cases v with
      | Err e =>
        simp [phi, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame, post, convW]
      | Ok x =>
        have ih' := ih out S q (ws ++ [x]) (by simp; omega)
        unfold PCVU_Fresh2.verifier.read_checkpoint_weights_loop at ih'
        rw [hb] at ih'
        have e1 : (⟨(dwS S q ws).setAtNat (q + ws.length) x, q + ws.length + 1⟩ : core.slice.iter.IterMut KK) =
            ⟨dwS S q (ws ++ [x]), q + (ws ++ [x]).length⟩ := by
          simp [dw_snoc]
        have e2 : (fun im : core.slice.iter.IterMut KK =>
              ({ im with slice := owS (im.slice.setAtNat (q + ws.length) x) q ws } : core.slice.iter.IterMut KK)) =
            (fun im => {im with slice := owS im.slice q (ws ++ [x])}) := by
          funext im
          simp [ow_snoc]
        simpa [phi, core.result.Result.Insts.CoreOpsTry.branch, e1, e2] using ih'

#print axioms loop_claim

def intoIterM (v : alloc.vec.Vec KK) :
    Result (core.slice.iter.IterMut KK × (core.slice.iter.IterMut KK → alloc.vec.Vec KK)) :=
  ok (⟨⟨v.val, v.property⟩, 0⟩, fun it => ⟨it.slice.val, it.slice.property⟩)

theorem weights_eq (bytes : Slice Std.U8) (at1 : Std.Usize) (v : alloc.vec.Vec KK) :
    PCVU_Fresh2.verifier.read_checkpoint_weights fle0 intoIterM bytes at1 v =
      (CheckpointBytes4Ops.readWeights bytes at1 v >>= fun r => ok (phi r)) := by
  have h := loop_claim v.val.length ⟨bytes, at1⟩ ⟨v.val, v.property⟩ 0 [] (by simp)
  unfold PCVU_Fresh2.verifier.read_checkpoint_weights CheckpointBytes4Ops.readWeights CheckpointBytes4Ops.weightsUsing
  simp only [intoIterM, bind_assoc, bind_tc_ok]
  try dsimp only
  try dsimp only at h
  refine Eq.trans ?_ (Eq.trans h ?_)
  · congr 1
    funext res
    rcases res with ⟨at2, pending, back⟩
    cases pending <;> rfl
  · simp only [bind_assoc, bind_tc_ok]
    congr 1
    funext res
    cases res with
    | Err e => rfl
    | Ok pr => rcases pr with ⟨it, r⟩; rfl

#print axioms weights_eq
end PCVU_Rd
