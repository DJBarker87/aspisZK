import NPH_R22Direct

/-! NPH_ (R22, 2026-11-10 continuation, item 1): the multiproof traversal invariant for
MultiproofConeRef.reference.binary_step. Lemmas about the existing gate definitions; nothing merged
changes, and no hash totality is assumed.

binary_step has five checked operations: i + 1, i + 2, len(nodes) - s.at (both arms), and s.at + 32.
- i + 1 follows a successful read s.idx[i] on a 16-entry array, and i + 2 follows a successful
  read s.idx[i + 1] (`succ_after_read`, `two_after_read`): ok for every input.
- len(nodes) - s.at has no guard of its own. `AtInv nodes s` (s.at <= len nodes) is the traversal
  invariant. On it the subtraction is ok with the exact difference (`gap_ok`), so the wrapping
  difference is the same value, the Stop test `< 32` takes the same branch in both profiles, and
  s.at + 32 is ok and <= len nodes (`advance_ok`).
- `step_next`: every successful Next step of binary_step keeps AtInv, keeps n, and advances i.
  The new cursor is either s.at (the paired-sibling arm) or s.at + 32 after the range read
  nodes[s.at, s.at + 32) succeeded.
- `rows_done`: every Done result of level_rows from an AtInv state is an AtInv state.
- `Reached` is the set of traversal states: verify_owned's (and Port9OR_P6Verify.factored's)
  entry {s with at := 0} into levels, closed under the Next step of binary_step (the level_rows
  recursion) and under the Done result of level_rows (the levels recursion). `reached_inv`: every
  reached state satisfies AtInv. `reached_ops`: at every reached state every checked operation of
  binary_step that executes is ok, with the mathematical value.
The call structure (binary_step is called only by level_rows, level_rows only by levels, levels only
by verify_owned and Port9OR_P6Verify.factored, both entering at at := 0) is read from the gate text
and the backward referrer screen NPH_REFS7.json (textual, flagged). Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22Binary
open Aeneas Aeneas.Std Result MultiproofConeRef AspisR1.NPH_R22FieldRef

abbrev Dg (X : Type) := MultiproofConeRef.aspis_core.digest.Digest32 X

/-- The traversal invariant over the multiproof scratch state. -/
def AtInv (nodes : Slice U8) (s : reference.Scratch) : Prop := s.«at».val ≤ nodes.val.length

theorem len_val (nodes : Slice U8) : (Slice.len nodes).val = nodes.val.length := by
  first | rfl | simp [Slice.len_val] | simp [Slice.len] | scalar_tac

theorem index_lt {α : Type} {n : Usize} (v : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize v i = ok x) : i.val < v.val.length := by
  by_contra hge
  have hn : v.val[i.val]? = none := List.getElem?_eq_none (by omega)
  first
  | (simp [Array.index_usize, Array.getElem?_Usize_eq, hn] at h)
  | (unfold Array.index_usize at h; simp [hn] at h)
  | (unfold Array.index_usize at h; split at h <;> simp_all [Array.getElem?_Usize_eq])
  | (unfold Array.index_usize at h; split at h <;> simp_all)

theorem idx_len (s : reference.Scratch) : s.idx.val.length = 16 := by
  first | exact s.idx.property | simpa using s.idx.property

/-! ### The checked operations of binary_step -/

theorem succ_after_read (s : reference.Scratch) (i : Usize) (x : U32)
    (h : Array.index_usize s.idx i = ok x) :
    ∃ z, (i + 1#usize : Result Usize) = ok z ∧ z.val = i.val + 1 := by
  have hl := index_lt s.idx i x h
  rw [idx_len] at hl
  exact NPH_R22Loops.usize_succ_ok i 16#usize (by scalar_tac)

theorem two_after_read (s : reference.Scratch) (i i1 : Usize) (x : U32) (hi1 : i1.val = i.val + 1)
    (h : Array.index_usize s.idx i1 = ok x) :
    ∃ z, (i + 2#usize : Result Usize) = ok z ∧ z.val = i.val + 2 := by
  have hl := index_lt s.idx i1 x h
  rw [idx_len] at hl
  have h2 : (2#usize : Usize).val = 2 := by first | rfl | simp | decide
  have hmax : 32 ≤ UScalar.max .Usize := by scalar_tac
  have hm : i.val + (2#usize : Usize).val ≤ UScalar.max .Usize := by rw [h2]; omega
  obtain ⟨z, hz, hv⟩ := add_ok i 2#usize hm
  exact ⟨z, hz, by rw [hv, h2]⟩

theorem gap_ok (nodes : Slice U8) (s : reference.Scratch) (inv : AtInv nodes s) :
    ∃ z, (Slice.len nodes - s.«at» : Result Usize) = ok z ∧ z.val = nodes.val.length - s.«at».val := by
  have hl := len_val nodes
  have hle : s.«at».val ≤ (Slice.len nodes).val := by rw [hl]; exact inv
  obtain ⟨z, hz, hv⟩ := sub_ok (Slice.len nodes) s.«at» hle
  exact ⟨z, hz, by rw [hv, hl]⟩

theorem advance_ok (nodes : Slice U8) (s : reference.Scratch) (z : Usize)
    (hz : z.val = nodes.val.length - s.«at».val) (inv : AtInv nodes s) (big : ¬ z < 32#usize) :
    ∃ c, (s.«at» + 32#usize : Result Usize) = ok c ∧ c.val = s.«at».val + 32 ∧
      c.val ≤ nodes.val.length := by
  have h32 : (32#usize : Usize).val = 32 := by first | rfl | simp | decide
  have hb : 32 ≤ z.val := by
    first
    | scalar_tac
    | (have hn : ¬ z.val < (32#usize : Usize).val := big; rw [h32] at hn; omega)
  have hlen := NPH_R22Loops5.slice_len_le nodes
  unfold AtInv at inv
  have hm : s.«at».val + (32#usize : Usize).val ≤ UScalar.max .Usize := by rw [h32]; omega
  obtain ⟨c, hc, hv⟩ := add_ok s.«at» 32#usize hm
  refine ⟨c, hc, by rw [hv, h32], ?_⟩
  rw [hv, h32]; omega

/-! ### Preservation -/

theorem wp_next {X : Type} {D : Dg X} {hash : X} {s : reference.Scratch}
    {l r : Array U8 32#usize} {ni c : Usize} {index : U32} {w : Usize}
    {s' : reference.Scratch} {j w' : Usize}
    (h : reference.write_parent D hash s l r ni c index w = ok (.Next s' j w')) :
    s'.«at» = c ∧ s'.n = s.n ∧ j = ni := by
  unfold reference.write_parent at h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  injection h with h1
  injection h1 with e1 e2 e3
  subst e1
  subst e2
  exact ⟨rfl, rfl, rfl⟩

/-- Every successful Next step keeps the invariant, keeps n and advances i. -/
theorem step_next {X : Type} (D : Dg X) (hash : X) (nodes : Slice U8) (s : reference.Scratch)
    (i w : Usize) (inv : AtInv nodes s) (s' : reference.Scratch) (i' w' : Usize)
    (h : reference.binary_step D hash s nodes i w = ok (.Next s' i' w')) :
    AtInv nodes s' ∧ s'.n = s.n ∧ i.val < i'.val := by
  unfold reference.binary_step at h
  try dsimp only at h
  obtain ⟨index, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨value, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨i1, hi1, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  have v1 : i1.val = i.val + 1 := by
    have := NPH_R22Cursor.add_val i 1#usize i1 hi1
    first | omega | (rw [this]; rfl) | (rw [this]; simp) | scalar_tac
  split at h
  · obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    split at h
    · obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      obtain ⟨i4, hi4, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      have v4 : i4.val = i.val + 2 := by
        have := NPH_R22Cursor.add_val i 2#usize i4 hi4
        first | omega | (rw [this]; rfl) | (rw [this]; simp) | scalar_tac
      obtain ⟨ea, en, ej⟩ := wp_next h
      refine ⟨?_, en, ?_⟩
      · unfold AtInv; rw [ea]; exact inv
      · rw [ej, v4]; omega
    · obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      split at h
      · simp at h
      · obtain ⟨i6, hi6, h⟩ := Port3_PushFrame.bind_success _ _ _ h
        obtain ⟨s1, hs1, h⟩ := Port3_PushFrame.bind_success _ _ _ h
        obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
        obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
        have rs := AspisR1.T2Nat_RawBounds.range_success nodes s1 s.«at» i6 hs1
        split at h
        · obtain ⟨ea, en, ej⟩ := wp_next h
          exact ⟨by unfold AtInv; rw [ea]; exact rs.2, en, by rw [ej, v1]; omega⟩
        · obtain ⟨ea, en, ej⟩ := wp_next h
          exact ⟨by unfold AtInv; rw [ea]; exact rs.2, en, by rw [ej, v1]; omega⟩
  · obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    split at h
    · simp at h
    · obtain ⟨i4, hi4, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      obtain ⟨s1, hs1, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      obtain ⟨_, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      have rs := AspisR1.T2Nat_RawBounds.range_success nodes s1 s.«at» i4 hs1
      split at h
      · obtain ⟨ea, en, ej⟩ := wp_next h
        exact ⟨by unfold AtInv; rw [ea]; exact rs.2, en, by rw [ej, v1]; omega⟩
      · obtain ⟨ea, en, ej⟩ := wp_next h
        exact ⟨by unfold AtInv; rw [ea]; exact rs.2, en, by rw [ej, v1]; omega⟩

/-- Every Done result of level_rows from an invariant state is an invariant state. -/
theorem rows_done {X : Type} (D : Dg X) (hash : X) (nodes : Slice U8) :
    ∀ (k : Nat) (s : reference.Scratch) (i w : Usize) (next : reference.Scratch),
      s.n.val - i.val ≤ k → AtInv nodes s →
      reference.level_rows D hash s nodes i w = ok (.Done next) → AtInv nodes next := by
  intro k
  induction k with
  | zero =>
    intro s i w next hk inv h
    have halt : i ≥ s.n := by change i.val ≥ s.n.val; omega
    rw [reference.level_rows] at h
    simp only [if_pos halt] at h
    have e : next = {s with n := w} := by
      injection h with h1
      injection h1 with h2
      exact h2.symm
    rw [e]; exact inv
  | succ k ih =>
    intro s i w next hk inv h
    rw [reference.level_rows] at h
    by_cases halt : i ≥ s.n
    · simp only [if_pos halt] at h
      have e : next = {s with n := w} := by
        injection h with h1
        injection h1 with h2
        exact h2.symm
      rw [e]; exact inv
    · simp only [if_neg halt] at h
      have hlt : i.val < s.n.val := by change ¬ i.val ≥ s.n.val at halt; omega
      obtain ⟨r, hr, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      cases r with
      | Stop s1 => simp at h
      | Next s' i' w' =>
        obtain ⟨a, en, ai⟩ := step_next D hash nodes s i w inv s' i' w' hr
        exact ih s' i' w' next (by rw [en]; omega) a h

/-! ### Reached traversal states -/

/-- The traversal states: the levels entry at at := 0, closed under the level_rows recursion
(a Next step of binary_step) and the levels recursion (a Done result of level_rows). -/
inductive Reached {X : Type} (D : Dg X) (hash : X) (nodes : Slice U8) : reference.Scratch → Prop
  | entry (s : reference.Scratch) : Reached D hash nodes {s with «at» := 0#usize}
  | row {s s' : reference.Scratch} {i w i' w' : Usize} : Reached D hash nodes s →
      reference.binary_step D hash s nodes i w = ok (.Next s' i' w') → Reached D hash nodes s'
  | level {s next : reference.Scratch} : Reached D hash nodes s →
      reference.level_rows D hash s nodes 0#usize 0#usize = ok (.Done next) →
      Reached D hash nodes next

theorem entry_inv (nodes : Slice U8) (s : reference.Scratch) :
    AtInv nodes {s with «at» := 0#usize} := by
  unfold AtInv
  show (0#usize : Usize).val ≤ nodes.val.length
  have : (0#usize : Usize).val = 0 := by first | rfl | simp | decide
  rw [this]; exact Nat.zero_le _

theorem reached_inv {X : Type} (D : Dg X) (hash : X) (nodes : Slice U8) (s : reference.Scratch)
    (h : Reached D hash nodes s) : AtInv nodes s := by
  induction h with
  | entry s => exact entry_inv nodes s
  | @row s s' i w i' w' _ step ih => exact (step_next D hash nodes s i w ih s' i' w' step).1
  | @level s next _ run ih => exact rows_done D hash nodes s.n.val s 0#usize 0#usize next (by omega) ih run

/-- At every reached traversal state every checked operation of binary_step that executes is ok,
with the mathematical value; in particular len(nodes) - s.at never wraps. -/
theorem reached_ops {X : Type} (D : Dg X) (hash : X) (nodes : Slice U8) (s : reference.Scratch)
    (h : Reached D hash nodes s) (i : Usize) :
    (∀ x, Array.index_usize s.idx i = ok x →
        ∃ z, (i + 1#usize : Result Usize) = ok z ∧ z.val = i.val + 1) ∧
    (∀ i1 x, i1.val = i.val + 1 → Array.index_usize s.idx i1 = ok x →
        ∃ z, (i + 2#usize : Result Usize) = ok z ∧ z.val = i.val + 2) ∧
    (∃ z, (Slice.len nodes - s.«at» : Result Usize) = ok z ∧
        z.val = nodes.val.length - s.«at».val ∧
        (¬ z < 32#usize → ∃ c, (s.«at» + 32#usize : Result Usize) = ok c ∧
          c.val = s.«at».val + 32 ∧ c.val ≤ nodes.val.length)) := by
  have inv := reached_inv D hash nodes s h
  refine ⟨fun x hx => succ_after_read s i x hx, fun i1 x e hx => two_after_read s i i1 x e hx, ?_⟩
  obtain ⟨z, hz, hv⟩ := gap_ok nodes s inv
  exact ⟨z, hz, hv, fun big => advance_ok nodes s z hv inv big⟩

#print axioms len_val
#print axioms index_lt
#print axioms succ_after_read
#print axioms two_after_read
#print axioms gap_ok
#print axioms advance_ok
#print axioms wp_next
#print axioms step_next
#print axioms rows_done
#print axioms entry_inv
#print axioms reached_inv
#print axioms reached_ops
end AspisR1.NPH_R22Binary
