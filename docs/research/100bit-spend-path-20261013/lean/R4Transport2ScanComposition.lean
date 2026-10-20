import QueryScanRow31Invariant
import R1QueryTruncation

/-! Single-word contracts, their loop invariant, and the selected-state driver.
The source splice and Kani steps live in tools/r4-transport2-kit. -/
set_option autoImplicit false
namespace AspisR1.R4Transport2ScanComposition
open AspisV8R19.Q22WordScan AspisV8R19.SamplerWords
open AspisV8R19.SourceDuplexStep

def wordStep (s : ScanState) (x : Nat) : ScanState × Bool :=
  if s.accepted.length = 22 ∨ s.draws = 64 then (s,true)
  else (⟨keep s.accepted x,s.draws+1⟩,false)

def runSteps {S : Type} (step : S → Nat → S × Bool) : S → List Nat → S × Bool
  | s, [] => (s,false)
  | s, x::xs => let r := step s x
               if r.2 then r else runSteps step r.1 xs

/-- A proved single-step relation suffices for any length of scanner loop.
The hypothesis is the complete state relation, including the stop flag. -/
theorem scan_loop_refines {S : Type} (view : S → ScanState)
    (step : S → Nat → S × Bool)
    (hstep : ∀ s x, (view (step s x).1, (step s x).2) = wordStep (view s) x)
    (s : S) (xs : List Nat) :
    (view (runSteps step s xs).1, (runSteps step s xs).2) = scan (view s) xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have h := hstep s x
    have hs := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    by_cases stop : (view s).accepted.length = 22 ∨ (view s).draws = 64
    · simp only [wordStep, if_pos stop] at hs hb
      simp only [runSteps, hb, if_true, scan, if_pos stop]
      exact Prod.ext hs rfl
    · simp only [wordStep, if_neg stop] at hs hb
      simp only [runSteps, hb, Bool.false_eq_true, if_false, scan, if_neg stop]
      rw [← hs]
      exact ih (step s x).1

/-- The invariant needed at the next word is preserved even on stop. -/
theorem wordStep_invariant (s : ScanState) (x : Nat)
    (hlen : s.accepted.length ≤ 22) (hdraws : s.draws ≤ 64)
    (hn : s.accepted.Nodup) :
    (wordStep s x).1.accepted.length ≤ 22 ∧
    (wordStep s x).1.draws ≤ 64 ∧ (wordStep s x).1.accepted.Nodup := by
  by_cases stop : s.accepted.length = 22 ∨ s.draws = 64
  · simpa only [wordStep, if_pos stop] using And.intro hlen (And.intro hdraws hn)
  · simp only [wordStep, if_neg stop]
    have hk := keep_length s.accepted x
    exact ⟨by omega, by omega, QueryScanOrderedModel.keep_nodup _ _ hn⟩

/-- Materialized digest pairs: the return state is the advance of the block
whose scan detects stop, including detection in the *following* block. -/
def pairsRun (s : ScanState) : List (State × State) → State →
    Except Nat (List Nat) × State
  | [], last => (finish s,last)
  | (block,advanced)::ps, _ =>
    let r := scan s (words 18 block)
    if r.2 then (finish r.1,advanced) else pairsRun r.1 ps advanced

/-- The missing draws guard in the materialized-pairs caller is harmless on
its reached loop invariant. No distinctness assumption on advances is used. -/
theorem pairsRun_scanOut (ps : List (State × State)) (s : ScanState) (last : State)
    (hbudget : s.draws + 8*ps.length ≤ 64) :
    pairsRun s ps last = R0C.V3.Q22.scanOut ps.length s
      (ps.map Prod.fst) (ps.map Prod.snd) last := by
  induction ps generalizing s last with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨b,a⟩
    have hdraws : s.draws < 64 := by simp only [List.length_cons] at hbudget; omega
    simp only [pairsRun, List.length_cons, List.map_cons, R0C.V3.Q22.scanOut,
      if_pos hdraws]
    by_cases hs : (scan s (words 18 b)).2 = true
    · simp only [hs, if_true]
    · simp only [hs, Bool.false_eq_true, if_false]
      apply ih
      have hf : (scan s (words 18 b)).2 = false := Bool.eq_false_iff.mpr hs
      have hp := scan_progress s (words 18 b) hf
      have hw : (words 18 b).length = 8 := by simp [words]
      rw [hw] at hp
      simp only [List.length_cons] at hbudget
      omega

/-- Eight materialized pairs return exactly the model's selected advance. -/
theorem eight_pairs_selected (ps : List (State × State)) (last : State)
    (hlen : ps.length = 8) :
    pairsRun R0C.V3.Q22.q0 ps last = R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0
      (ps.map Prod.fst) (ps.map Prod.snd) last := by
  simpa only [hlen] using pairsRun_scanOut ps R0C.V3.Q22.q0 last
    (by simp [R0C.V3.Q22.q0, hlen])

#print axioms scan_loop_refines
#print axioms wordStep_invariant
#print axioms pairsRun_scanOut
#print axioms eight_pairs_selected
end AspisR1.R4Transport2ScanComposition
