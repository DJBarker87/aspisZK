-- PCVA_ P3a (class SOURCE_SHAPE, loop return encoding; FP3-2 of PCUC_FOR_P3.json).
-- Fresh (p2 pass, PCQC_E003) digest_is_canonical_loop returns Option Bool (pending_return); the gate returns Bool.
-- Fresh `aspis_core.field.P` is an opaque `Result U32` in the received fresh emission (FP3-1, owned by P1e).  HYPOTHESIS H_P below:
-- the P1e-transparent form `P = ok <gate P>`.  Every theorem here is conditional on exactly H_P; it is NOT discharged by this file.
import Aeneas
import AspisR1TerminalDecoder.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace PRVFresh_TD
open AspisR1TerminalDecoder

/-- H_P: P1e-transparent fresh form of aspis_core::field::P (conditional hypothesis, see header). -/
def aspis_core.field.P : Result Std.U32 := ok AspisR1TerminalDecoder.aspis_core.field.P

def pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
  (digest : Array aspis_core.field.M31 8#usize) (i : Std.Usize) :
  Result (ControlFlow Std.Usize (Option Bool))
  := do
  let s ← lift (Array.to_slice digest)
  let i1 := Slice.len s
  if i < i1
  then
    let m ← Array.index_usize digest i
    let i2 ← PRVFresh_TD.aspis_core.field.P
    if m >= i2
    then ok (done (some false))
    else let i3 ← i + 1#usize
         ok (cont i3)
  else ok (done none)

def pool_v1.pair_forest_accounts.digest_is_canonical_loop
  (digest : Array aspis_core.field.M31 8#usize) (i : Std.Usize) :
  Result (Option Bool)
  := do
  loop
    (fun i1 => PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
      digest i1)
    i

def pool_v1.pair_forest_accounts.digest_is_canonical
  (digest : Array aspis_core.field.M31 8#usize) : Result Bool := do
  let pending_return ←
    PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop digest 0#usize
  match pending_return with
  | none => ok true
  | some b => ok b

end PRVFresh_TD

namespace PRVP3

def conv : Option Bool → Bool
  | none => true
  | some b => b

/-- body-level refinement: the gate body is the fresh body with the pending-return encoding forgotten. -/
theorem body_refines (digest : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize) (i : Std.Usize) :
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i =
    (PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i) >>= fun cf =>
      ok (match cf with | cont j => cont j | done o => done (conv o)) := by
  unfold AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body PRVFresh_TD.aspis_core.field.P
  simp only [lift, bind_tc_ok]
  by_cases h : i < Slice.len (Array.to_slice digest)
  · simp only [h, if_true, bind_tc_ok]
    rcases hm : Array.index_usize digest i with m | e | _ <;> simp [hm]
    · by_cases hp : (AspisR1TerminalDecoder.aspis_core.field.P).val ≤ m.val <;> simp [hp, conv]
  · simp only [h, if_false, bind_tc_ok, conv]
#print axioms body_refines

theorem body_cont (digest : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize) (i j : Std.Usize)
    (h : PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i = ok (cont j)) :
    i.val < 8 ∧ j.val = i.val + 1 := by
  unfold PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body PRVFresh_TD.aspis_core.field.P at h
  simp only [lift, bind_tc_ok] at h
  have hlen : (Slice.len (Array.to_slice digest)).val = 8 := by
    simp [Slice.len, Array.to_slice]
  by_cases hi : i < Slice.len (Array.to_slice digest)
  · rw [if_pos hi] at h
    have hi8 : i.val < 8 := by
      have := hi; simp only [UScalar.lt_equiv] at this; omega
    refine ⟨hi8, ?_⟩
    rcases hm : Array.index_usize digest i with m | e | _
    · rw [hm] at h; simp only [bind_tc_ok] at h
      by_cases hp : m >= AspisR1TerminalDecoder.aspis_core.field.P
      · rw [if_pos hp] at h; simp at h
      · rw [if_neg hp] at h
        rcases hs : (i + 1#usize) with k | e | _
        · rw [hs] at h; simp only [bind_tc_ok] at h
          have hk := UScalar.add_equiv i 1#usize
          rw [hs] at hk
          injection h with h1; injection h1 with h2; subst h2
          simp at hk; omega
        · rw [hs] at h; simp at h
        · rw [hs] at h; simp at h
    · rw [hm] at h; simp at h
    · rw [hm] at h; simp at h
  · rw [if_neg hi] at h; simp at h

theorem loop_refines (digest : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize) :
    ∀ (n : Nat) (i : Std.Usize), 8 - i.val ≤ n →
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop digest i =
    (PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop digest i) >>= fun o => ok (conv o) := by
  intro n
  induction n with
  | zero | succ n ih =>
    all_goals
      intro i hi
      unfold AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop
        PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop
      rw [Aeneas.Std.loop.eq_1, Aeneas.Std.loop.eq_1, body_refines]
      rcases hb : PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i with r | e | _
      · simp only [bind_tc_ok]
        cases r with
        | done o => simp
        | cont j =>
          have hc := body_cont digest i j hb
          simp only [bind_tc_ok]
          first
            | (exfalso; omega)
            | (have := ih j (by omega)
               unfold AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop
                 PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop at this
               exact this)
      · simp
      · simp
#print axioms loop_refines

theorem digest_is_canonical_eq (digest : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize) :
    PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical digest =
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical digest := by
  unfold PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical
  rw [loop_refines digest 8 0#usize (by simp)]
  rcases hl : PRVFresh_TD.pool_v1.pair_forest_accounts.digest_is_canonical_loop digest 0#usize with o | e | _
  · cases o <;> simp [conv]
  · simp
  · simp
#print axioms digest_is_canonical_eq
end PRVP3
