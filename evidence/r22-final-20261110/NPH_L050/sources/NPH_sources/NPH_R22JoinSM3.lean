import RPz7_S1SemanticFinishModelV1
import OraclePortStdBuilder

/-! NPH_ (R22, SM step 2): generic congruence over the tx1 semantic finish and the verify prefix.
- `finish_congr`: FinishModel.finish with the mask/add/mul boundaries replaced by m'/a'/u' equals
  the original whenever the replacements agree with B at the arguments the finish actually
  passes: the mask at (fromFn 16 closureFn9 claims, fromFn 10 closureFn5 claims, claims[0][27],
  rounds alpha), the mul at (challenges.eta, the Ok terminal output), the first add at (the mask
  output, the mul output) and the second add at (that sum, decode(row 25, 87)[28]). Every
  argument is quantified only over values returned by the SAME successful earlier calls. Proof
  by bind-stepping through the finish body (both outcomes of every later step).
- `verify_congr`: VerifyPrefix.verify F equals VerifyPrefix.verify F' whenever F and F' agree on
  the (prefix, transcript, challenges) returned by the successful parse, public transcript and
  begin calls.
- `fromFn_mem` (induction over OraclePortStdBuilder.fromFnLoop): every element of a successful
  fromFn output is a call_mut output on the unchanged capture; `closure9_mem`/`closure5_mem`:
  closureFn6/closureFn2 return an element of claims[0] and keep the capture.
No producer is used here; standard axioms. -/
set_option autoImplicit false
set_option maxHeartbeats 40000
noncomputable section
namespace AspisR1.NPH_R22JoinSM3
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

abbrev Q := AspisR1PublicPreparation.aspis_core.field.QM31

theorem bind_congr_ok {α β : Type} (m : Result α) (k k' : α → Result β)
    (h : ∀ x, m = ok x → k x = k' x) : (m >>= k) = (m >>= k') := by
  cases m with
  | ok x => simp only [bind_tc_ok]; exact h x rfl
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]
#print axioms bind_congr_ok

theorem bind_ok_inv {α β : Type} {m : Result α} {k : α → Result β} {y : β}
    (h : (m >>= k) = ok y) : ∃ x, m = ok x ∧ k x = ok y := by
  cases m with
  | ok x => exact ⟨x, rfl, by simpa only [bind_tc_ok] using h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
#print axioms bind_ok_inv

theorem branch_cont {T E : Type} (r : core.result.Result T E) (v : T) :
    core.result.Result.Insts.CoreOpsTry.branch r =
      ok (core.ops.control_flow.ControlFlow.Continue v) ↔ r = .Ok v := by
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch]
#print axioms branch_cont

theorem map_err11_cont {H : Type} (D : aspis_core.Digest32 H)
    (r2 : core.result.Result Q aspis_core.state_only_prefix.r0.Error)
    (r3 : core.result.Result Q r1_wire.Error) (v : Q)
    (h3 : AspisR1PublicPreparation.core.result.Result.map_err (FinishModel.closureFn11 D) r2 () = ok r3)
    (hb : core.result.Result.Insts.CoreOpsTry.branch r3 = ok (core.ops.control_flow.ControlFlow.Continue v)) :
    r2 = .Ok v := by
  have e3 := (branch_cont r3 v).1 hb
  subst e3
  cases r2 with
  | Ok x =>
    simp only [AspisR1PublicPreparation.core.result.Result.map_err] at h3
    first | (cases h3; rfl) | simp_all
  | Err e =>
    simp [AspisR1PublicPreparation.core.result.Result.map_err, FinishModel.closureFn11,
      FinishModel.closureFn10, bind_tc_ok] at h3
#print axioms map_err11_cont

theorem idx_mem {α : Type} {n : Usize} (a : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize a i = ok x) : x ∈ a.val := by
  unfold Array.index_usize at h
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = ok x at h
  cases hg : a.val[i.val]? with
  | none => rw [hg] at h; cases h
  | some y =>
    rw [hg] at h
    cases h
    first
      | exact List.mem_of_getElem? hg
      | (obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp hg; rw [← he]; exact List.getElem_mem hl)
#print axioms idx_mem

theorem fromFnLoop_mem {C T : Type} (f : core.ops.function.FnMut C Usize T) (c : C) (P : T → Prop)
    (hf : ∀ i x c', f.call_mut c i = ok (x, c') → P x ∧ c' = c) :
    ∀ (is : List Usize) (xs : List T) (c'' : C),
      OraclePortStdBuilder.fromFnLoop f is c = ok (xs, c'') → ∀ x ∈ xs, P x := by
  intro is
  induction is with
  | nil =>
    intro xs c'' h x hx
    simp only [OraclePortStdBuilder.fromFnLoop] at h
    cases h
    simp at hx
  | cons i rest ih =>
    intro xs c'' h x hx
    simp only [OraclePortStdBuilder.fromFnLoop] at h
    obtain ⟨p, hp, h⟩ := bind_ok_inv h
    obtain ⟨y, c1⟩ := p
    obtain ⟨hy, hc1⟩ := hf i y c1 hp
    subst hc1
    obtain ⟨p2, hp2, h⟩ := bind_ok_inv h
    obtain ⟨ys, c2⟩ := p2
    cases h
    rcases List.mem_cons.mp hx with hxy | hxs
    · rw [hxy]; exact hy
    · exact ih ys c2 hp2 x hxs
#print axioms fromFnLoop_mem

theorem fromFn_mem {C T : Type} (n : Usize) (f : core.ops.function.FnMut C Usize T) (c : C)
    (P : T → Prop) (hf : ∀ i x c', f.call_mut c i = ok (x, c') → P x ∧ c' = c)
    (a : Array T n) (h : OraclePortStdBuilder.fromFn n f c = ok a) : ∀ x ∈ a.val, P x := by
  unfold OraclePortStdBuilder.fromFn at h
  obtain ⟨p, hp, h⟩ := bind_ok_inv h
  obtain ⟨xs, c2⟩ := p
  try dsimp only at h
  by_cases hl : xs.length = n.val
  · rw [dif_pos hl] at h
    cases h
    exact fromFnLoop_mem f c P hf _ xs c2 hp
  · rw [dif_neg hl] at h
    cases h
#print axioms fromFn_mem

theorem closure9_mem {H : Type} (D : aspis_core.Digest32 H) (c : FinishModel.Closure1 H)
    (P : Q → Prop) (hc : ∀ row ∈ c.val, ∀ q ∈ row.val, P q) :
    ∀ i x c', (FinishModel.closureFn9 D).call_mut c i = ok (x, c') → P x ∧ c' = c := by
  intro i x c' h
  change FinishModel.closureFn6 D c i = ok (x, c') at h
  unfold FinishModel.closureFn6 at h
  obtain ⟨a, ha, h⟩ := bind_ok_inv h
  obtain ⟨q, hq, h⟩ := bind_ok_inv h
  cases h
  exact ⟨hc a (idx_mem _ _ _ ha) x (idx_mem _ _ _ hq), rfl⟩
#print axioms closure9_mem

theorem closure5_mem {H : Type} (D : aspis_core.Digest32 H) (c : FinishModel.Closure2 H)
    (P : Q → Prop) (hc : ∀ row ∈ c.val, ∀ q ∈ row.val, P q) :
    ∀ i x c', (FinishModel.closureFn5 D).call_mut c i = ok (x, c') → P x ∧ c' = c := by
  intro i x c' h
  change FinishModel.closureFn2 D c i = ok (x, c') at h
  unfold FinishModel.closureFn2 at h
  obtain ⟨j, hj, h⟩ := bind_ok_inv h
  obtain ⟨a, ha, h⟩ := bind_ok_inv h
  obtain ⟨q, hq, h⟩ := bind_ok_inv h
  cases h
  exact ⟨hc a (idx_mem _ _ _ ha) x (idx_mem _ _ _ hq), rfl⟩

abbrev Claims := Array (Array Q 29#usize) 3#usize
#print axioms closure5_mem

theorem circle_eq (B : FinishModel.Boundaries)
    (m' : Array Q 16#usize → Array Q 10#usize → Q → Array Q 10#usize → Result Q)
    (a' u' : Q → Q → Result Q) {H : Type} (D : aspis_core.Digest32 H)
    (s : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord) :
    FinishModel.circle_validated { B with mask := m', add := a', mul := u' } D s rec =
      FinishModel.circle_validated B D s rec := by
  unfold FinishModel.circle_validated
  dsimp only
  try rfl
#print axioms circle_eq

theorem finish_congr (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (m' : Array Q 16#usize → Array Q 10#usize → Q → Array Q 10#usize → Result Q)
    (a' u' : Q → Q → Result Q)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (hmask : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize) (q : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a →
      B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 →
      Array.index_usize v1 0#usize = ok a2 → Array.index_usize a2 27#usize = ok q →
      m' a a1 q alpha = B.mask a a1 q alpha)
    (hmul : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.terminal pub v1 alpha ch = ok (.Ok val2) →
      u' ch.eta val2 = B.mul ch.eta val2)
    (hadd1 : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize)
      (q mk q1 : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.terminal pub v1 alpha ch = ok (.Ok val2) →
      B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a →
      B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 →
      Array.index_usize v1 0#usize = ok a2 → Array.index_usize a2 27#usize = ok q →
      B.mask a a1 q alpha = ok mk → B.mul ch.eta val2 = ok q1 →
      a' mk q1 = B.add mk q1)
    (hadd2 : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize)
      (q mk q1 q2 : Q) (vr : r1_wire.ValidatedRecord) (val3 : Array Q 29#usize) (q3 : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.terminal pub v1 alpha ch = ok (.Ok val2) →
      B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a →
      B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 →
      Array.index_usize v1 0#usize = ok a2 → Array.index_usize a2 27#usize = ok q →
      B.mask a a1 q alpha = ok mk → B.mul ch.eta val2 = ok q1 → B.add mk q1 = ok q2 →
      r1_wire.Prefix.validated_record pre 25#u8 = ok (.Ok vr) →
      R.decode 29#usize vr 87#usize = ok (.Ok val3) →
      Array.index_usize val3 28#usize = ok q3 →
      a' q2 q3 = B.add q2 q3) :
    FinishModel.finish R { B with mask := m', add := a', mul := u' } D pub pre t ch obs =
      FinishModel.finish R B D pub pre t ch obs := by
  unfold FinishModel.finish
  refine bind_congr_ok _ _ _ (fun r hr => ?_)
  refine bind_congr_ok _ _ _ (fun cf hcf => ?_)
  cases cf with
  | Break res => dsimp only
  | Continue val =>
  obtain ⟨running, alpha, t1⟩ := val
  have hR : RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) := by
    rw [hr, (branch_cont r _).1 hcf]
  try dsimp only
  refine bind_congr_ok _ _ _ (fun u2 _ => ?_)
  refine bind_congr_ok _ _ _ (fun r1 hr1 => ?_)
  refine bind_congr_ok _ _ _ (fun cf1 hcf1 => ?_)
  cases cf1 with
  | Break res => dsimp only
  | Continue v1 =>
  have hC : B.claims pre = ok (.Ok v1) := by
    have e := (branch_cont r1 _).1 hcf1; subst e; exact hr1
  refine bind_congr_ok _ _ _ (fun r2 hr2 => ?_)
  refine bind_congr_ok _ _ _ (fun r3 hr3 => ?_)
  refine bind_congr_ok _ _ _ (fun cf2 hcf2 => ?_)
  cases cf2 with
  | Break res => dsimp only
  | Continue val2 =>
  have hT : B.terminal pub v1 alpha ch = ok (.Ok val2) := by
    have e := map_err11_cont D r2 r3 val2 hr3 hcf2; subst e; exact hr2
  refine bind_congr_ok _ _ _ (fun u3 _ => ?_)
  refine bind_congr_ok _ _ _ (fun a ha => ?_)
  refine bind_congr_ok _ _ _ (fun a1 ha1 => ?_)
  refine bind_congr_ok _ _ _ (fun a2 ha2 => ?_)
  refine bind_congr_ok _ _ _ (fun q hq => ?_)
  have hm := hmask running alpha t1 v1 a a1 a2 q hR hC ha ha1 ha2 hq
  show (m' a a1 q alpha >>= _) = _
  rw [hm]
  refine bind_congr_ok _ _ _ (fun mk hmk => ?_)
  refine bind_congr_ok _ _ _ (fun r4 hr4 => ?_)
  refine bind_congr_ok _ _ _ (fun cf3 hcf3 => ?_)
  cases cf3 with
  | Break res => dsimp only
  | Continue vr =>
  have hV : r1_wire.Prefix.validated_record pre 25#u8 = ok (.Ok vr) := by
    have e := (branch_cont r4 _).1 hcf3; subst e; exact hr4
  refine bind_congr_ok _ _ _ (fun r5 hr5 => ?_)
  refine bind_congr_ok _ _ _ (fun cf4 hcf4 => ?_)
  cases cf4 with
  | Break res => dsimp only
  | Continue val3 =>
  have hD : R.decode 29#usize vr 87#usize = ok (.Ok val3) := by
    have e := (branch_cont r5 _).1 hcf4; subst e; exact hr5
  have hu := hmul running alpha t1 v1 val2 hR hC hT
  show (u' ch.eta val2 >>= _) = _
  rw [hu]
  refine bind_congr_ok _ _ _ (fun q1 hq1 => ?_)
  have hx1 := hadd1 running alpha t1 v1 val2 a a1 a2 q mk q1 hR hC hT ha ha1 ha2 hq hmk hq1
  show (a' mk q1 >>= _) = _
  rw [hx1]
  refine bind_congr_ok _ _ _ (fun q2 hq2 => ?_)
  refine bind_congr_ok _ _ _ (fun q3 hq3 => ?_)
  have hx2 := hadd2 running alpha t1 v1 val2 a a1 a2 q mk q1 q2 vr val3 q3 hR hC hT ha ha1 ha2 hq
    hmk hq1 hq2 hV hD hq3
  show (a' q2 q3 >>= _) = _
  rw [hx2]
  refine bind_congr_ok _ _ _ (fun mt _ => ?_)
  refine bind_congr_ok _ _ _ (fun b _ => ?_)
  (try simp only [circle_eq]) <;> (try dsimp only)
#print axioms finish_congr

theorem verify_congr (F F' : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (h : ∀ (p : r1_wire.Prefix) (t t' : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges),
      PrefixAdapter.parseAccepted bytes = ok (.Ok p) →
      r1_semantic.public_transcript D pub hash p.c1_root = ok (.Ok t) →
      r1_wire.begin D p t = ok (.Ok c, t') →
      F D pub p t' c obs = F' D pub p t' c obs) :
    VerifyPrefix.verify F D pub bytes hash obs = VerifyPrefix.verify F' D pub bytes hash obs := by
  unfold VerifyPrefix.verify
  refine bind_congr_ok _ _ _ (fun r hr => ?_)
  refine bind_congr_ok _ _ _ (fun cf hcf => ?_)
  cases cf with
  | Break res => dsimp only
  | Continue p =>
  have hP : PrefixAdapter.parseAccepted bytes = ok (.Ok p) := by
    have e := (branch_cont r _).1 hcf; subst e; exact hr
  refine bind_congr_ok _ _ _ (fun u0 _ => ?_)
  refine bind_congr_ok _ _ _ (fun r1 hr1 => ?_)
  refine bind_congr_ok _ _ _ (fun cf1 hcf1 => ?_)
  cases cf1 with
  | Break res => dsimp only
  | Continue t =>
  have hT : r1_semantic.public_transcript D pub hash p.c1_root = ok (.Ok t) := by
    have e := (branch_cont r1 _).1 hcf1; subst e; exact hr1
  refine bind_congr_ok _ _ _ (fun x hx => ?_)
  obtain ⟨r2, t'⟩ := x
  try dsimp only
  refine bind_congr_ok _ _ _ (fun cf2 hcf2 => ?_)
  cases cf2 with
  | Break res => dsimp only
  | Continue c =>
  have hB : r1_wire.begin D p t = ok (.Ok c, t') := by
    have e := (branch_cont r2 _).1 hcf2; subst e; exact hx
  refine bind_congr_ok _ _ _ (fun u1 _ => ?_)
  exact h p t t' c hP hT hB
#print axioms verify_congr

end AspisR1.NPH_R22JoinSM3