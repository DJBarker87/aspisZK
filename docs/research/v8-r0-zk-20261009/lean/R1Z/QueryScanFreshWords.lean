import R1Z.QueryScanFreshProgram
import R1Z.QueryScanRealLazyBound

/-! The retained squeeze/advance scan fragment, with the exact independent
LE parser law on fresh reads. The prefix table is arbitrary and consistent. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanFreshWords
open R0Z R0Z.FsStatement R0Z.FsAbort R1Z.GamesR1 R1Z.LensR1 R1Z.QueryScanFreshProgram
  R1Z.QueryScanPrivacyFinal R1Z.QueryScanRealLazyBound
  R1Z.QueryScanSharedHistoryObstruction
  AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
attribute [local instance] Classical.propDecidable

/-- The scan fragment has no counter/salt added to either retained input. -/
def queries : (n : ℕ) → OracleAnswer → Marked (List UInt8) OracleAnswer n
  | 0, _ => .done
  | n+1, s => .scan (squeezeAddress s) (fun _ =>
      .other (advanceAddress s) (fun next => queries n next))

def freshFlag : ℕ → OracleAnswer → Finset (List UInt8) →
    (List UInt8 → OracleAnswer) → Bool
  | 0, _, _, _ => true
  | n+1, s, seen, H => decide (squeezeAddress s ∉ seen) &&
      freshFlag n (H (advanceAddress s)) (insert (advanceAddress s) (insert (squeezeAddress s) seen)) H

theorem query_state_shift (H : List UInt8 → OracleAnswer) (s : OracleAnswer) (n : ℕ) :
    queryState H s (n+1) = queryState H (H (advanceAddress s)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change H (advanceAddress (queryState H s (n+1))) =
        H (advanceAddress (queryState H (H (advanceAddress s)) n))
      rw [ih]

/-- Compiled interpreter identity, symbolic in the block count and oracle.
The returned blocks are the same shared-ROM reads used by queryBlocks. -/
theorem queries_eval {O : Type} (n : ℕ) (s : OracleAnswer)
    (seen : Finset (List UInt8)) (H : List UInt8 → OracleAnswer)
    (out : Bool × (Fin n → OracleAnswer) → O) :
    (eval H (compile (queries n s) seen out)).2 =
      out (freshFlag n s seen H, fun j => H (squeezeAddress (queryState H s j.val))) := by
  induction n generalizing s seen with
  | zero =>
      apply congrArg out
      apply Prod.ext
      · rfl
      · exact Subsingleton.elim _ _
  | succ n ih =>
      simp only [queries, compile, eval]
      rw [ih]
      congr 1
      apply Prod.ext
      · rfl
      · funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · simp only [Fin.cons_succ, Fin.val_succ, query_state_shift]

/-- Any eight marked calls, including interleaved memoized unmarked calls,
satisfy the existing selected-stop LE failure bound on fresh histories. -/
theorem fresh_program_scan_le {I : Type} [DecidableEq I] [Fintype I]
    (p : Marked I OracleAnswer 8) :
    mean (fun H : I → OracleAnswer =>
      let r := (eval H (compile p ∅ id)).2
      if r.1 = true ∧ parserBad r.2 then (1 : ℚ) else 0) ≤ scanProbability :=
  (fresh_oracle_bound p parserBad).trans parser_bad_mass

/-- Exact squeeze/advance fragment from ANY fixed prior history. This is a
fresh subevent bound, not a bound conditional on every revealed answer. -/
theorem fresh_query_fragment_le (s : OracleAnswer)
    (t : Table (List UInt8) OracleAnswer) (seen : Finset (List UInt8))
    (ht : Consistent t seen) :
    lazyMean (compile (queries 8 s) seen id) t
      (fun v => if v.2.1 = true ∧ parserBad v.2.2 then (1 : ℚ) else 0) ≤ scanProbability := by
  have hh := lazy_fresh_bound (queries 8 s) t seen ht id
    (fun r => if r.1 = true ∧ parserBad r.2 then (1 : ℚ) else 0)
    (fun q => if parserBad q then (1 : ℚ) else 0)
    (fun q => by split_ifs <;> norm_num)
    (by intro b q; cases b <;> simp)
  exact hh.trans parser_bad_mass

#print axioms query_state_shift
#print axioms queries_eval
#print axioms fresh_program_scan_le
#print axioms fresh_query_fragment_le
end R1Z.QueryScanFreshWords
