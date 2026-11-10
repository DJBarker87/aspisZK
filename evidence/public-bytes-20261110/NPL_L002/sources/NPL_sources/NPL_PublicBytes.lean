-- NPL_PublicBytes.lean (Stream A job NPL_, 2026-11-10)
-- The gate definition of `public_bytes` (and its callees) is proved equal to the hand transcription
-- NPL_PublicBytesRef of the frozen Rust accessor; plus totality and output length.
import Aeneas
import AspisR1PublicPreparation.Funs
import NPL_PublicBytesRef
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NPL_PublicBytes
open AspisR1PublicPreparation

/-! ## 1. Gate = transcription -/

theorem P_eq : aspis_core.field.P = NPL_PublicBytesRef.P := by
  first
    | (unfold aspis_core.field.P NPL_PublicBytesRef.P; rfl)
    | (with_unfolding_all rfl)
    | (simp [aspis_core.field.P, NPL_PublicBytesRef.P])

theorem private_public_eq :
    pool_v1.pair_forest_semantic_terminal.private_public = NPL_PublicBytesRef.private_public := by
  funext a b; rfl

theorem withdrawal_public_eq :
    pool_v1.pair_forest_semantic_terminal.withdrawal_public = NPL_PublicBytesRef.withdrawal_public := by
  funext a b; rfl

theorem semantic_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.semantic = NPL_PublicBytesRef.semantic := by
  funext self; cases self <;> rfl

theorem fields_loop_body_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body =
      NPL_PublicBytesRef.fields_loop.body := by
  funext iter out
  unfold pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
    NPL_PublicBytesRef.fields_loop.body
  first
    | rw [P_eq]
    | simp only [P_eq]
  all_goals rfl

theorem fields_loop_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop =
      NPL_PublicBytesRef.fields_loop := by
  funext iter out
  unfold pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop
    NPL_PublicBytesRef.fields_loop
  first
    | rw [fields_loop_body_eq]
    | simp only [fields_loop_body_eq]
  all_goals rfl

theorem fields_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields = NPL_PublicBytesRef.fields := by
  funext out values
  unfold pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields NPL_PublicBytesRef.fields
  first
    | rw [fields_loop_eq]
    | simp only [fields_loop_eq]
  all_goals rfl

theorem frontier_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier = NPL_PublicBytesRef.frontier := by
  funext out values
  unfold pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier NPL_PublicBytesRef.frontier
  first
    | rw [fields_eq]
    | simp only [fields_eq]
  all_goals first
    | rfl
    | (simp only [NPL_PublicBytesRef.tryUnit]; rfl)

/-- Main equality: the gate constant equals the hand transcription of the frozen accessor. -/
theorem gate_eq :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes = NPL_PublicBytesRef.public_bytes := by
  funext self
  cases self <;>
    (unfold pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes NPL_PublicBytesRef.public_bytes
     first
       | rw [fields_eq, frontier_eq, semantic_eq]
       | simp only [fields_eq, frontier_eq, semantic_eq]
     all_goals first
       | rfl
       | (simp only [NPL_PublicBytesRef.semantic, NPL_PublicBytesRef.private_public, NPL_PublicBytesRef.withdrawal_public, bind_tc_ok,
           NPL_PublicBytesRef.tryTop, NPL_PublicBytesRef.ifSomeFields]; rfl))

/-! ## 2. Totality and output length -/

abbrev Good (n : Nat) (res : Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) ×
    (alloc.vec.Vec Std.U8))) : Prop :=
  ∃ r out', res = ok (r, out') ∧ (r = core.result.Result.Ok () → out'.val.length = n)

abbrev TGood (n : Nat) (res : Result (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_core.state_only_prefix.r0.Error)) : Prop :=
  ∃ r, res = ok r ∧ ∀ v, r = core.result.Result.Ok v → v.val.length = n

theorem usize_ge : 4294967295 ≤ Usize.max := by
  first
    | scalar_tac
    | (rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max, U64.max, U32.numBits, U64.numBits])
    | (rcases Usize.bounds_eq with h | h <;> rw [h] <;> decide)

macro "npl_idx" : tactic => `(tactic| first | scalar_tac | (simp; scalar_tac) | decide | simp)

theorem len_slice {α : Type} {n : Usize} (a : Array α n) :
    (Array.to_slice a).val.length = n.val := a.property

theorem len_lit8 {α : Type} (a : Array α 8#usize) : (Array.to_slice a).val.length = 8 := by
  rw [len_slice]; first | rfl | simp | scalar_tac

theorem len_lit4 {α : Type} (a : Array α 4#usize) : (Array.to_slice a).val.length = 4 := by
  rw [len_slice]; first | rfl | simp | scalar_tac

theorem len_one {α : Type} (x : α) :
    (Array.to_slice (Array.make 1#usize [ x ])).val.length = 1 := by
  first | rfl | simp [Array.to_slice, Array.make] | scalar_tac

theorem extend_good (v : alloc.vec.Vec Std.U8) (s : Slice Std.U8)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    ∃ v' : alloc.vec.Vec Std.U8, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = ok v' ∧
      v'.val.length = v.val.length + s.val.length := by
  obtain ⟨s', hc, hss⟩ := WP.spec_imp_exists
    (Slice.clone_spec (clone := core.clone.CloneU8.clone) (s := s) (fun x _ => rfl))
  unfold alloc.vec.Vec.extend_from_slice
  split
  · split
    · rename_i s'' heq
      refine ⟨_, rfl, ?_⟩
      have hl := Slice.clone_length heq
      simp only [Slice.length] at hl
      simp only [List.length_append, hl]
    · rename_i e heq; rw [hc] at heq; cases heq
    · rename_i heq; rw [hc] at heq; cases heq
  · rename_i hh; exact absurd h hh

theorem push_good (v : alloc.vec.Vec Std.U8) (x : Std.U8) (h : v.val.length + 1 ≤ Usize.max) :
    ∃ v', alloc.vec.Vec.push v x = ok v' ∧ v'.val.length = v.val.length + 1 := by
  obtain ⟨v', hv, hl⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec v x (by omega))
  exact ⟨v', hv, by rw [hl, List.length_append]; rfl⟩

theorem next_some {α : Type} (s : Slice α) (i : Nat) (hi : i < s.val.length) :
    ∃ x, core.slice.iter.IteratorSliceIter.next (⟨s, i⟩ : core.slice.iter.Iter α) =
      ok (some x, ⟨s, i + 1⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · exact ⟨_, rfl⟩
  · rename_i hc; exfalso; apply hc; simpa [Slice.len_val] using hi

theorem next_none {α : Type} (s : Slice α) (i : Nat) (hi : ¬ i < s.val.length) :
    core.slice.iter.IteratorSliceIter.next (⟨s, i⟩ : core.slice.iter.Iter α) = ok (none, ⟨s, i⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · rename_i hc; exfalso; apply hi; simpa [Slice.len_val] using hc
  · rfl

theorem body_done (s : Slice aspis_core.field.M31) (i : Nat) (out : alloc.vec.Vec Std.U8)
    (hi : ¬ i < s.val.length) :
    NPL_PublicBytesRef.fields_loop.body ⟨s, i⟩ out = ok (done (core.result.Result.Ok (), out)) := by
  unfold NPL_PublicBytesRef.fields_loop.body
  rw [next_none s i hi]
  all_goals first | rfl | simp

theorem body_step (s : Slice aspis_core.field.M31) (i : Nat) (out : alloc.vec.Vec Std.U8)
    (hi : i < s.val.length) (hb : out.val.length + 4 ≤ Usize.max) :
    (∃ e, NPL_PublicBytesRef.fields_loop.body ⟨s, i⟩ out = ok (done (core.result.Result.Err e, out))) ∨
    (∃ out', NPL_PublicBytesRef.fields_loop.body ⟨s, i⟩ out = ok (cont (⟨s, i + 1⟩, out')) ∧
      out'.val.length = out.val.length + 4) := by
  obtain ⟨x, hx⟩ := next_some s i hi
  have h1 : NPL_PublicBytesRef.fields_loop.body ⟨s, i⟩ out =
      (if x >= NPL_PublicBytesRef.P then
        ok (done (core.result.Result.Err aspis_core.state_only_prefix.r0.Error.Public, out))
      else do
        let a ← lift (core.num.U32.to_le_bytes x)
        let s' ← lift (Array.to_slice a)
        let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s'
        ok (cont ((⟨s, i + 1⟩ : core.slice.iter.Iter aspis_core.field.M31), out1))) := by
    unfold NPL_PublicBytesRef.fields_loop.body
    rw [hx]
    all_goals rfl
  rw [h1]
  by_cases hp : x >= NPL_PublicBytesRef.P
  · left
    exact ⟨aspis_core.state_only_prefix.r0.Error.Public, by rw [if_pos hp]⟩
  · right
    obtain ⟨v', hv, hl⟩ := extend_good out (Array.to_slice (core.num.U32.to_le_bytes x))
      (by rw [len_lit4]; exact hb)
    refine ⟨v', ?_, by rw [hl, len_lit4]⟩
    rw [if_neg hp]
    simp only [lift, bind_tc_ok, hv]

theorem fields_loop_good (s : Slice aspis_core.field.M31) :
    ∀ (k i : Nat) (out : alloc.vec.Vec Std.U8), s.val.length = i + k →
      out.val.length + 4 * k ≤ Usize.max →
      Good (out.val.length + 4 * k) (NPL_PublicBytesRef.fields_loop ⟨s, i⟩ out) := by
  intro k
  induction k with
  | zero =>
    intro i out hs hb
    have hd := body_done s i out (by omega)
    unfold NPL_PublicBytesRef.fields_loop
    first | rw [Aeneas.Std.loop] | rw [Aeneas.Std.loop.eq_1] | unfold Aeneas.Std.loop
    simp only [hd]
    exact ⟨_, out, rfl, fun _ => by omega⟩
  | succ k ih =>
    intro i out hs hb
    rcases body_step s i out (by omega) (by omega) with ⟨e, he⟩ | ⟨out', he, hl⟩
    · unfold NPL_PublicBytesRef.fields_loop
      first | rw [Aeneas.Std.loop] | rw [Aeneas.Std.loop.eq_1] | unfold Aeneas.Std.loop
      simp only [he]
      exact ⟨_, out, rfl, fun h => by cases h⟩
    · have ih' := ih (i + 1) out' (by omega) (by omega)
      have e : out'.val.length + 4 * k = out.val.length + 4 * (k + 1) := by omega
      rw [e] at ih'
      unfold NPL_PublicBytesRef.fields_loop at ih' ⊢
      first | rw [Aeneas.Std.loop] | rw [Aeneas.Std.loop.eq_1] | unfold Aeneas.Std.loop
      simp only [he]
      exact ih'

theorem fields_good (out : alloc.vec.Vec Std.U8) (s : Slice aspis_core.field.M31) (n c : Nat)
    (hn : out.val.length = n) (hc : s.val.length = c) (hb : n + 4 * c ≤ Usize.max) :
    Good (n + 4 * c) (NPL_PublicBytesRef.fields out s) := by
  have := fields_loop_good s c 0 out (by omega) (by omega)
  rw [hn] at this
  unfold NPL_PublicBytesRef.fields
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_tc_ok,
    bind_ok]
  exact this

theorem tryUnit_good {m n : Nat} {x : Result ((core.result.Result Unit
    aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))}
    {k : alloc.vec.Vec Std.U8 → Result ((core.result.Result Unit
    aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))}
    (hx : Good n x) (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n → Good m (k o)) :
    Good m (NPL_PublicBytesRef.tryUnit x k) := by
  obtain ⟨r, o, hx, hr⟩ := hx
  cases r with
  | Ok u =>
    cases u
    have := hk o (hr rfl)
    simpa [NPL_PublicBytesRef.tryUnit, hx, core.result.Result.Insts.CoreOpsTry.branch] using this
  | Err e =>
    refine ⟨core.result.Result.Err e, o, ?_, fun h => by cases h⟩
    simp [NPL_PublicBytesRef.tryUnit, hx, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]

theorem tryTop_good {m n : Nat} {x : Result ((core.result.Result Unit
    aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8))}
    {k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_core.state_only_prefix.r0.Error)}
    (hx : Good n x) (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n → TGood m (k o)) :
    TGood m (NPL_PublicBytesRef.tryTop x k) := by
  obtain ⟨r, o, hx, hr⟩ := hx
  cases r with
  | Ok u =>
    cases u
    have := hk o (hr rfl)
    simpa [NPL_PublicBytesRef.tryTop, hx, core.result.Result.Insts.CoreOpsTry.branch] using this
  | Err e =>
    refine ⟨core.result.Result.Err e, ?_, fun v h => by cases h⟩
    simp [NPL_PublicBytesRef.tryTop, hx, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]

theorem idx_step {m : Nat} (values : Array (Array aspis_core.field.M31 8#usize) 20#usize)
    (j : Usize) (hj : j.val < values.val.length) (out : alloc.vec.Vec Std.U8)
    (k : alloc.vec.Vec Std.U8 → Result ((core.result.Result Unit
      aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8)))
    (hb : out.val.length + 32 ≤ Usize.max)
    (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = out.val.length + 32 → Good m (k o)) :
    Good m (do
      let a ← Array.index_usize values j
      let s ← lift (Array.to_slice a)
      NPL_PublicBytesRef.tryUnit (NPL_PublicBytesRef.fields out s) k) := by
  obtain ⟨a, ha, -⟩ := WP.spec_imp_exists (Array.index_usize_spec values j hj)
  rw [ha]
  simp only [bind_tc_ok, bind_ok, lift]
  exact tryUnit_good (fields_good out (Array.to_slice a) _ 8 rfl (len_lit8 a) (by omega)) hk

theorem frontier_good (out : alloc.vec.Vec Std.U8)
    (values : Array (Array aspis_core.field.M31 8#usize) 20#usize)
    (hb : out.val.length + 640 ≤ Usize.max) :
    Good (out.val.length + 640) (NPL_PublicBytesRef.frontier out values) := by
  unfold NPL_PublicBytesRef.frontier
  refine idx_step values _ (by npl_idx) out _ (by omega) (fun o1 h1 => ?_)
  refine idx_step values _ (by npl_idx) o1 _ (by omega) (fun o2 h2 => ?_)
  refine idx_step values _ (by npl_idx) o2 _ (by omega) (fun o3 h3 => ?_)
  refine idx_step values _ (by npl_idx) o3 _ (by omega) (fun o4 h4 => ?_)
  refine idx_step values _ (by npl_idx) o4 _ (by omega) (fun o5 h5 => ?_)
  refine idx_step values _ (by npl_idx) o5 _ (by omega) (fun o6 h6 => ?_)
  refine idx_step values _ (by npl_idx) o6 _ (by omega) (fun o7 h7 => ?_)
  refine idx_step values _ (by npl_idx) o7 _ (by omega) (fun o8 h8 => ?_)
  refine idx_step values _ (by npl_idx) o8 _ (by omega) (fun o9 h9 => ?_)
  refine idx_step values _ (by npl_idx) o9 _ (by omega) (fun o10 h10 => ?_)
  refine idx_step values _ (by npl_idx) o10 _ (by omega) (fun o11 h11 => ?_)
  refine idx_step values _ (by npl_idx) o11 _ (by omega) (fun o12 h12 => ?_)
  refine idx_step values _ (by npl_idx) o12 _ (by omega) (fun o13 h13 => ?_)
  refine idx_step values _ (by npl_idx) o13 _ (by omega) (fun o14 h14 => ?_)
  refine idx_step values _ (by npl_idx) o14 _ (by omega) (fun o15 h15 => ?_)
  refine idx_step values _ (by npl_idx) o15 _ (by omega) (fun o16 h16 => ?_)
  refine idx_step values _ (by npl_idx) o16 _ (by omega) (fun o17 h17 => ?_)
  refine idx_step values _ (by npl_idx) o17 _ (by omega) (fun o18 h18 => ?_)
  refine idx_step values _ (by npl_idx) o18 _ (by omega) (fun o19 h19 => ?_)
  refine idx_step values _ (by npl_idx) o19 _ (by omega) (fun o20 h20 => ?_)
  exact ⟨_, o20, rfl, fun _ => by omega⟩

theorem top_push {m n : Nat} {v : alloc.vec.Vec Std.U8} {x : Std.U8}
    {k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8)
      aspis_core.state_only_prefix.r0.Error)}
    (hn : v.val.length = n) (hb : n + 1 ≤ Usize.max)
    (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n + 1 → TGood m (k o)) :
    TGood m (alloc.vec.Vec.push v x >>= k) := by
  obtain ⟨v', hv, hl⟩ := push_good v x (by omega)
  rw [hv]; simp only [bind_tc_ok, bind_ok]; exact hk v' (by omega)

theorem top_extend {m n c : Nat} {v : alloc.vec.Vec Std.U8} {s : Slice Std.U8}
    {k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8)
      aspis_core.state_only_prefix.r0.Error)}
    (hn : v.val.length = n) (hc : s.val.length = c) (hb : n + c ≤ Usize.max)
    (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n + c → TGood m (k o)) :
    TGood m (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s >>= k) := by
  obtain ⟨v', hv, hl⟩ := extend_good v s (by omega)
  rw [hv]; simp only [bind_tc_ok, bind_ok]; exact hk v' (by omega)

theorem top_fields {m n c : Nat} {out : alloc.vec.Vec Std.U8} {s : Slice aspis_core.field.M31}
    {k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8)
      aspis_core.state_only_prefix.r0.Error)}
    (hn : out.val.length = n) (hc : s.val.length = c) (hb : n + 4 * c ≤ Usize.max)
    (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n + 4 * c → TGood m (k o)) :
    TGood m (NPL_PublicBytesRef.tryTop (NPL_PublicBytesRef.fields out s) k) :=
  tryTop_good (fields_good out s n c hn hc hb) hk

theorem top_frontier {m n : Nat} {out : alloc.vec.Vec Std.U8}
    {values : Array (Array aspis_core.field.M31 8#usize) 20#usize}
    {k : alloc.vec.Vec Std.U8 → Result (core.result.Result (alloc.vec.Vec Std.U8)
      aspis_core.state_only_prefix.r0.Error)}
    (hn : out.val.length = n) (hb : n + 640 ≤ Usize.max)
    (hk : ∀ o : alloc.vec.Vec Std.U8, o.val.length = n + 640 → TGood m (k o)) :
    TGood m (NPL_PublicBytesRef.tryTop (NPL_PublicBytesRef.frontier out values) k) := by
  have := frontier_good out values (by omega)
  rw [hn] at this
  exact tryTop_good this hk

/-- Expected output length: Transfer 1+32+32+4+1+32+32+1+8+640+32+640 = 1455;
    Withdrawal 1+32+32+4+1+32+1+4+8+640+32+640 = 1427. -/
def expected_len : pool_v1.pair_forest_semantic_terminal.r0.Public → Nat
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer _ _ => 1455
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal _ _ => 1427

theorem ref_public_bytes_good (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
    TGood (expected_len self) (NPL_PublicBytesRef.public_bytes self) := by
  have U := usize_ge
  cases self with
  | Transfer pub1 tr =>
    simp only [NPL_PublicBytesRef.public_bytes, NPL_PublicBytesRef.semantic, NPL_PublicBytesRef.private_public, NPL_PublicBytesRef.ifSomeFields, lift,
      bind_tc_ok, bind_ok, expected_len]
    refine top_push (n := 0) rfl (by omega) (fun o1 h1 => ?_)
    refine top_fields h1 (len_lit8 _) (by omega) (fun o2 h2 => ?_)
    refine top_fields h2 (len_lit8 _) (by omega) (fun o3 h3 => ?_)
    refine top_fields h3 (len_one _) (by omega) (fun o4 h4 => ?_)
    refine top_push h4 (by omega) (fun o5 h5 => ?_)
    refine top_fields h5 (len_lit8 _) (by omega) (fun o6 h6 => ?_)
    refine top_fields h6 (len_lit8 _) (by omega) (fun o7 h7 => ?_)
    refine top_push h7 (by omega) (fun o8 h8 => ?_)
    refine top_extend h8 (len_lit8 _) (by omega) (fun o9 h9 => ?_)
    refine top_frontier h9 (by omega) (fun o10 h10 => ?_)
    refine top_fields h10 (len_lit8 _) (by omega) (fun o11 h11 => ?_)
    refine top_frontier h11 (by omega) (fun o12 h12 => ?_)
    exact ⟨_, rfl, fun v hv => by cases hv; omega⟩
  | Withdrawal pub1 tr =>
    simp only [NPL_PublicBytesRef.public_bytes, NPL_PublicBytesRef.semantic, NPL_PublicBytesRef.withdrawal_public, NPL_PublicBytesRef.ifSomeFields, lift,
      bind_tc_ok, bind_ok, expected_len]
    refine top_push (n := 0) rfl (by omega) (fun o1 h1 => ?_)
    refine top_fields h1 (len_lit8 _) (by omega) (fun o2 h2 => ?_)
    refine top_fields h2 (len_lit8 _) (by omega) (fun o3 h3 => ?_)
    refine top_fields h3 (len_one _) (by omega) (fun o4 h4 => ?_)
    refine top_push h4 (by omega) (fun o5 h5 => ?_)
    refine top_fields h5 (len_lit8 _) (by omega) (fun o6 h6 => ?_)
    refine top_push h6 (by omega) (fun o7 h7 => ?_)
    refine top_fields h7 (len_one _) (by omega) (fun o8 h8 => ?_)
    refine top_extend h8 (len_lit8 _) (by omega) (fun o9 h9 => ?_)
    refine top_frontier h9 (by omega) (fun o10 h10 => ?_)
    refine top_fields h10 (len_lit8 _) (by omega) (fun o11 h11 => ?_)
    refine top_frontier h11 (by omega) (fun o12 h12 => ?_)
    exact ⟨_, rfl, fun v hv => by cases hv; omega⟩

/-- Totality and output length for the GATE constant: on every input the gate returns `ok`
    (never `fail`/`div`, i.e. the modelled Rust body never panics), and an `Ok v` result has
    exactly `expected_len self` bytes. -/
theorem gate_total_length (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
    ∃ r, pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes self = ok r ∧
      ∀ v, r = core.result.Result.Ok v → v.val.length = expected_len self := by
  rw [gate_eq]; exact ref_public_bytes_good self

end NPL_PublicBytes

#print axioms NPL_PublicBytes.P_eq
#print axioms NPL_PublicBytes.private_public_eq
#print axioms NPL_PublicBytes.withdrawal_public_eq
#print axioms NPL_PublicBytes.semantic_eq
#print axioms NPL_PublicBytes.fields_loop_body_eq
#print axioms NPL_PublicBytes.fields_loop_eq
#print axioms NPL_PublicBytes.fields_eq
#print axioms NPL_PublicBytes.frontier_eq
#print axioms NPL_PublicBytes.gate_eq
#print axioms NPL_PublicBytes.gate_total_length
