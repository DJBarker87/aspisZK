
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
    core.slice.iter.IteratorIterMut.next (⟨S, i⟩ : core.slice.iter.IterMut KK) =
      ok (some (S.val[i]'h), (⟨S, i + 1⟩ : core.slice.iter.IterMut KK),
        fun it' x => match x with | none => it' | some x => {it' with slice := it'.slice.setAtNat i x}) := by
  first
    | (simp [core.slice.iter.IteratorIterMut.next, h]; done)
    | (simp [core.slice.iter.IteratorIterMut.next, h]; exact ⟨rfl, rfl⟩)
    | (simp [core.slice.iter.IteratorIterMut.next, h]; refine ⟨rfl, ?_⟩; funext it' x; cases x <;> rfl)

theorem next_none (S : Slice KK) (i : Nat) (h : ¬ i < S.val.length) :
    core.slice.iter.IteratorIterMut.next (⟨S, i⟩ : core.slice.iter.IterMut KK) =
      ok (none, (⟨S, i⟩ : core.slice.iter.IterMut KK), fun it _ => it) := by
  have h' : ¬ i < (S.len : Std.Usize).val := by rw [Slice.len_val]; simpa [Slice.length] using h
  simp only [core.slice.iter.IteratorIterMut.next]
  rw [dif_neg h']

theorem loop_step (fle : Slice Std.U8 → Result (Option KK)) (iter : core.slice.iter.IterMut KK)
    (back : core.slice.iter.IterMut KK → core.slice.iter.IterMut KK) (bytes : Slice Std.U8) (at1 : Std.Usize) :
    PCVU_Fresh2.verifier.read_checkpoint_weights_loop fle iter back bytes at1 =
      (PCVU_Fresh2.verifier.read_checkpoint_weights_loop.body fle bytes iter back at1 >>= fun cf =>
        match cf with
        | ControlFlow.cont st => PCVU_Fresh2.verifier.read_checkpoint_weights_loop fle st.1 st.2.1 bytes st.2.2
        | ControlFlow.done y => ok y) := by
  unfold PCVU_Fresh2.verifier.read_checkpoint_weights_loop
  rw [loop_unfold, bs_bind]
  first
    | with_unfolding_all rfl
    | (congr 1; funext cf; cases cf with
        | cont st => rfl
        | done y => rfl)

theorem body_none (fle : Slice Std.U8 → Result (Option KK)) (S : Slice KK) (i : Nat) (h : ¬ i < S.val.length)
    (back : core.slice.iter.IterMut KK → core.slice.iter.IterMut KK) (bytes : Slice Std.U8) (at1 : Std.Usize) :
    PCVU_Fresh2.verifier.read_checkpoint_weights_loop.body fle bytes ⟨S, i⟩ back at1 =
      ok (ControlFlow.done (at1, none, back ⟨S, i⟩)) := by
  unfold PCVU_Fresh2.verifier.read_checkpoint_weights_loop.body
  rw [next_none S i h]
  rfl

theorem body_some (S : Slice KK) (i : Nat) (h : i < S.val.length)
    (back : core.slice.iter.IterMut KK → core.slice.iter.IterMut KK) (bytes : Slice Std.U8) (at1 : Std.Usize) :
    PCVU_Fresh2.verifier.read_checkpoint_weights_loop.body fle0 bytes ⟨S, i⟩ back at1 =
      (PCVU_Fresh2.verifier.Reader.k fle0 ⟨bytes, at1⟩ >>= fun (rr, reader) => (do
        let cf ← core.result.Result.Insts.CoreOpsTry.branch rr
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
            ok (ControlFlow.cont ((⟨S, i + 1⟩ : core.slice.iter.IterMut KK),
              (fun (im : core.slice.iter.IterMut KK) => back {im with slice := im.slice.setAtNat i val}), reader.«at»))
        | core.ops.control_flow.ControlFlow.Break residual => do
            let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec KK × Std.Usize) (core.convert.FromSame VErr) residual
            ok (ControlFlow.done (at1, some r1,
              back {(⟨S, i + 1⟩ : core.slice.iter.IterMut KK) with
                slice := (⟨S, i + 1⟩ : core.slice.iter.IterMut KK).slice.setAtNat i (S[i]'h)})))) := by
  unfold PCVU_Fresh2.verifier.read_checkpoint_weights_loop.body
  rw [next_some S i h]
  rfl

theorem wl_succ (n : Nat) (r : verifier.Reader) (it : core.slice.iter.IterMut KK) (h : it.i < it.slice.val.length) :
    CheckpointBytes4Sections.weightLoop CheckpointBytes3Reader.readK (n + 1) r it =
      (CheckpointBytes3Reader.readK r >>= fun (value, out) =>
        match value with
        | .Err e => ok (.Err e)
        | .Ok y => CheckpointBytes4Sections.weightLoop CheckpointBytes3Reader.readK n out
            ⟨it.slice.setAtNat it.i y, it.i + 1⟩) := by
  rw [CheckpointBytes4Sections.weightLoop]
  rw [next_some it.slice it.i h]
  rfl

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
    rw [loop_step, body_none fle0 S _ hn]
    simp [CheckpointBytes4Sections.weightLoop, post, convW, dw_eq_ow]
  | succ n ih =>
    intro r S q ws h
    have hlt : q + ws.length < S.val.length := by omega
    have hlt' : q + ws.length < (dwS S q ws).val.length := by rw [dw_length]; exact hlt
    rw [loop_step, body_some S _ hlt, wl_succ n r ⟨dwS S q ws, q + ws.length⟩ hlt']
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
        rw [hb] at ih'
        have e2 : (fun im : core.slice.iter.IterMut KK =>
              ({ im with slice := owS (im.slice.setAtNat (q + ws.length) x) q ws } : core.slice.iter.IterMut KK)) =
            (fun im => {im with slice := owS im.slice q (ws ++ [x])}) := by
          funext im
          simp [ow_snoc]
        simpa [phi, core.result.Result.Insts.CoreOpsTry.branch, e2, dw_snoc, Nat.add_assoc] using ih'
    all_goals omega

#print axioms loop_claim

def intoIterM (v : alloc.vec.Vec KK) :
    Result (core.slice.iter.IterMut KK × (core.slice.iter.IterMut KK → alloc.vec.Vec KK)) :=
  ok (⟨⟨v.val, v.property⟩, 0⟩, fun it => ⟨it.slice.val, it.slice.property⟩)

theorem weights_eq (bytes : Slice Std.U8) (at1 : Std.Usize) (v : alloc.vec.Vec KK) :
    PCVU_Fresh2.verifier.read_checkpoint_weights fle0 intoIterM bytes at1 v =
      (CheckpointBytes4Ops.readWeights bytes at1 v >>= fun r => ok (phi r)) := by
  have h := loop_claim v.val.length ⟨bytes, at1⟩ ⟨v.val, v.property⟩ 0 [] (by simp)
  have hpost : ∀ res : Std.Usize × (Option (core.result.Result (alloc.vec.Vec KK × Std.Usize) VErr)) × (core.slice.iter.IterMut KK),
      (match res with
        | (at2, pending, back) => match pending with
          | none => (ok (core.result.Result.Ok (⟨back.slice.val, back.slice.property⟩, at2)) :
              Result (core.result.Result (alloc.vec.Vec KK × Std.Usize) VErr))
          | some r => ok r) = ok (post res) := by
    rintro ⟨at2, pending, back⟩
    cases pending <;> rfl
  have step1 : PCVU_Fresh2.verifier.read_checkpoint_weights fle0 intoIterM bytes at1 v =
      (PCVU_Fresh2.verifier.read_checkpoint_weights_loop fle0 ⟨⟨v.val, v.property⟩, 0⟩ (fun im => im) bytes at1
        >>= fun res => ok (post res)) := by
    unfold PCVU_Fresh2.verifier.read_checkpoint_weights
    change (PCVU_Fresh2.verifier.read_checkpoint_weights_loop fle0 ⟨⟨v.val, v.property⟩, 0⟩ (fun im => im) bytes at1
        >>= fun res => match res with
          | (at2, pending, back) => match pending with
            | none => ok (core.result.Result.Ok (⟨back.slice.val, back.slice.property⟩, at2))
            | some r => ok r) = _
    congr 1
    funext res
    exact hpost res
  rw [step1]
  refine Eq.trans h ?_
  unfold CheckpointBytes4Ops.readWeights CheckpointBytes4Ops.weightsUsing
  simp only [bind_assoc, bind_tc_ok]
  congr 1
  funext res
  cases res with
  | Err e => rfl
  | Ok pr => rcases pr with ⟨it, r⟩; rfl

#print axioms weights_eq
