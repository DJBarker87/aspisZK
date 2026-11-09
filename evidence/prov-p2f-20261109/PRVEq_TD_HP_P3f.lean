-- PCUF_ P2f (scope item 2): discharge of the hypothesis H_P of the P3a conditional loop refinement (PCVA_L050, PRVEq_AspisR1TerminalDecoder_FunsLoop_P3.lean).
-- Fresh declarations: verbatim PCQF_E002 (P1e, overflow checks ON, aspis_core.field.P transparent) Funs.lean (sha256 a04f47ae218ca5f4b36303b0524b78b50adc5820ee3c377c36400eb6b5c5d1d4), registration attributes stripped,
-- namespace PCQF_aspis_statement_pool_v1_pair_forest_accounts -> AspisR1TerminalDecoder.PRVFresh_TDf. There is NO hypothesis: the fresh `aspis_core.field.P` is the emitted `def P : Std.U32 := 2147483647#u32` and P_eq proves it equal to the gate P.
import Aeneas
import AspisR1TerminalDecoder.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1TerminalDecoder
namespace PRVFresh_TDf

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [aspis_statement::pool_v1::pair_forest_accounts::digest_is_canonical]: loop body 0:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 168:4-175:1 -/
def pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
  (digest : Array aspis_core.field.M31 8#usize) (i : Std.Usize) :
  Result (ControlFlow Std.Usize (Option Bool))
  := do
  let s ← lift (Array.to_slice digest)
  let i1 := Slice.len s
  if i < i1
  then
    let m ← Array.index_usize digest i
    if m >= aspis_core.field.P
    then ok (done (some false))
    else let i2 ← i + 1#usize
         ok (cont i2)
  else ok (done none)

/-- [aspis_statement::pool_v1::pair_forest_accounts::digest_is_canonical]: loop 0:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 168:4-175:1 -/
def pool_v1.pair_forest_accounts.digest_is_canonical_loop
  (digest : Array aspis_core.field.M31 8#usize) (i : Std.Usize) :
  Result (Option Bool)
  := do
  loop
    (fun i1 => pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
      digest i1)
    i

/-- [aspis_statement::pool_v1::pair_forest_accounts::digest_is_canonical]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 166:0-175:1 -/
def pool_v1.pair_forest_accounts.digest_is_canonical
  (digest : Array aspis_core.field.M31 8#usize) : Result Bool := do
  let pending_return ←
    pool_v1.pair_forest_accounts.digest_is_canonical_loop digest 0#usize
  match pending_return with
  | none => ok true
  | some b => ok b

/-- [aspis_statement::pool_v1::pair_forest_accounts::first_canonical_byte]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 178:0-180:1 -/
def pool_v1.pair_forest_accounts.first_canonical_byte
  (digest : Array aspis_core.field.M31 8#usize) : Result Std.U8 := do
  let a ← atomic_statement.encode_digest_canonical digest
  Array.index_usize a 0#usize

/-- [aspis_statement::pool_v1::pair_forest_accounts::pool_v1_pair_forest_output_lane_v1]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 184:0-191:1
    Visibility: public -/
def pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
  (nullifier : Array aspis_core.field.M31 8#usize) :
  Result (core.result.Result Std.U8
    pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  := do
  let b ← pool_v1.pair_forest_accounts.digest_is_canonical nullifier
  if b
  then
    let i ← pool_v1.pair_forest_accounts.first_canonical_byte nullifier
    let i1 ← lift (i &&& 7#u8)
    ok (core.result.Result.Ok i1)
  else
    ok (core.result.Result.Err
      pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.NonCanonicalDigest)

end PRVFresh_TDf
end AspisR1TerminalDecoder

namespace PRVP3f

def conv : Option Bool → Bool
  | none => true
  | some b => b

/-- P_eq (replaces H_P): the fresh transparent P equals the gate P. -/
theorem P_eq : @AspisR1TerminalDecoder.PRVFresh_TDf.aspis_core.field.P = @AspisR1TerminalDecoder.aspis_core.field.P := by
  unfold AspisR1TerminalDecoder.PRVFresh_TDf.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl
#print axioms P_eq

theorem body_refines (digest : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize) (i : Std.Usize) :
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i =
    (AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i) >>= fun cf =>
      ok (match cf with | cont j => cont j | done o => done (conv o)) := by
  unfold AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
  rw [P_eq]
  simp only [lift, bind_tc_ok]
  by_cases h : i < Slice.len (Array.to_slice digest)
  · simp only [h, if_true, bind_tc_ok]
    rcases hm : Array.index_usize digest i with m | e | _ <;> simp [hm]
    · by_cases hp : (AspisR1TerminalDecoder.aspis_core.field.P).val ≤ m.val <;> simp [hp, conv]
  · simp only [h, if_false, bind_tc_ok, conv]
#print axioms body_refines

theorem body_cont (digest : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize) (i j : Std.Usize)
    (h : AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i = ok (cont j)) :
    i.val < 8 ∧ j.val = i.val + 1 := by
  unfold AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body at h
  rw [P_eq] at h
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
    (AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical_loop digest i) >>= fun o => ok (conv o) := by
  intro n
  induction n with
  | zero | succ n ih =>
    all_goals
      intro i hi
      unfold AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop
        AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical_loop
      rw [Aeneas.Std.loop.eq_1, Aeneas.Std.loop.eq_1, body_refines]
      rcases hb : AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i with r | e | _
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
                 AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical_loop at this
               exact this)
      · simp
      · simp
#print axioms loop_refines

theorem digest_is_canonical_eq (digest : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize) :
    AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical digest =
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical digest := by
  unfold AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical
  rw [loop_refines digest 8 0#usize (by simp)]
  rcases hl : AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical_loop digest 0#usize with o | e | _
  · cases o <;> simp [conv]
  · simp
  · simp
#print axioms digest_is_canonical_eq

theorem first_canonical_byte_eq : @AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.first_canonical_byte =
    @AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.first_canonical_byte := by
  unfold AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.first_canonical_byte AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.first_canonical_byte
  rfl
#print axioms first_canonical_byte_eq

theorem output_lane_eq : @AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 =
    @AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 := by
  funext nullifier
  unfold AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
  rw [digest_is_canonical_eq, first_canonical_byte_eq]
#print axioms output_lane_eq
end PRVP3f
