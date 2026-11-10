
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
  exact List.set_comm x y h _

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
    rw [ih (q + 1)]
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

theorem next_some (S : Slice KK) (i : Nat) (h : i < S.val.length) :
    core.slice.iter.IteratorIterMut.next (⟨S, i⟩ : core.slice.iter.IterMut KK) =
      ok (some (S.val[i]'h), (⟨S, i + 1⟩ : core.slice.iter.IterMut KK),
        fun it' x => match x with | none => it' | some x => {it' with slice := it'.slice.setAtNat i x}) := by
  have h' : i < (S.len : Std.Usize).val := by rw [Slice.len_val]; simpa [Slice.length] using h
  simp only [core.slice.iter.IteratorIterMut.next]
  rw [dif_pos h']
  rfl

theorem next_none (S : Slice KK) (i : Nat) (h : ¬ i < S.val.length) :
    core.slice.iter.IteratorIterMut.next (⟨S, i⟩ : core.slice.iter.IterMut KK) =
      ok (none, (⟨S, i⟩ : core.slice.iter.IterMut KK), fun it _ => it) := by
  have h' : ¬ i < (S.len : Std.Usize).val := by rw [Slice.len_val]; simpa [Slice.length] using h
  simp only [core.slice.iter.IteratorIterMut.next]
  rw [dif_neg h']

theorem dw_length (ws : List KK) : ∀ (s : Slice KK) (q : Nat), (dwS s q ws).val.length = s.val.length := by
  induction ws with
  | nil => intro s q; rfl
  | cons y ys ih =>
    intro s q
    simp only [dwS]
    rw [ih]
    exact Slice.setAtNat_length s q y

theorem readK_bytes (r : verifier.Reader) (v : core.result.Result KK VErr) (out : verifier.Reader)
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
    core.slice.iter.IteratorIterMut.next (⟨S, i⟩ : core.slice.iter.IterMut KK) =
      ok (some (S.val[i]'h), (⟨S, i + 1⟩ : core.slice.iter.IterMut KK),
        fun it' x => match x with | none => it' | some x => {it' with slice := it'.slice.setAtNat i x}) := by
  have h' : i < (S.len : Std.Usize).val := by rw [Slice.len_val]; simpa [Slice.length] using h
  simp only [core.slice.iter.IteratorIterMut.next]
  rw [dif_pos h']
  rfl

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
    rw [next_none S _ hn]
    simp [CheckpointBytes4Sections.weightLoop, post, convW, dw_eq_ow]
  | succ n ih =>
    intro r S q ws h
    have hlt : q + ws.length < S.val.length := by omega
    have hlt' : q + ws.length < (dwS S q ws).val.length := by rw [dw_length]; exact hlt
    unfold PCVU_Fresh2.verifier.read_checkpoint_weights_loop
    rw [loop_unfold, bs_bind]
    unfold PCVU_Fresh2.verifier.read_checkpoint_weights_loop.body
    rw [next_some S _ hlt]
    simp only [CheckpointBytes4Sections.weightLoop]
    rw [next_some (dwS S q ws) _ hlt']
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
