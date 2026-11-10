
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
