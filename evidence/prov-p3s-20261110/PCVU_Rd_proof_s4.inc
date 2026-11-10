
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
