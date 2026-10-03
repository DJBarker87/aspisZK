import AspisV8R19.QM31SamplerProgram

set_option autoImplicit false
namespace AspisV8R19.R444InitialSourceLimb
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SamplerWords
abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Bytes := AspisV8R19.DuplexFrames.Bytes

/-- Scan masked words using the source sentinel; the count is consumed words. -/
def sourceScan : List Nat → Option Nat × Nat
  | [] => (none, 0)
  | w :: ws =>
      if w = 2147483647 then
        let tail := sourceScan ws
        (tail.1, tail.2 + 1)
      else (some w, 1)

/-- The bounded suffix of the current block, with each source word masked. -/
def blockSuffix (block : State) (i : Nat) : (n : Nat) → i + n ≤ 8 → List Nat
  | 0, _ => []
  | n + 1, h =>
      masked 31 (word block ⟨i, by omega⟩) ::
        blockSuffix block (i + 1) n (by omega)

theorem blockSuffix_eq_ofFn (block : State) (i n : Nat) (h : i + n ≤ 8) :
    blockSuffix block i n h =
      List.ofFn (fun j : Fin n => masked 31 (word block ⟨i + j.val, by omega⟩)) := by
  induction n generalizing i with
  | zero => simp [blockSuffix]
  | succ n ih =>
      simp only [blockSuffix, List.ofFn_succ]
      simp only [List.cons.injEq]
      constructor
      · congr 1
        apply Fin.ext
        simp
      · have htail : i + 1 + n ≤ 8 := by omega
        rw [ih (i + 1) htail]
        apply congrArg List.ofFn
        funext j
        congr 1
        apply Fin.ext
        simp

theorem blockSuffix_full (block : State) :
    blockSuffix block 0 8 (by omega) = words 31 block := by
  rw [blockSuffix_eq_ofFn]
  simp [words]

def scanAt (block : State) (i n : Nat) (h : i + n ≤ 8) : Option Nat × Nat :=
  sourceScan (blockSuffix block i n h)

theorem limbRun_no_refill (H : Bytes → State) (n : Nat) (c : Cursor)
    (h : c.index.val + n ≤ 8) :
    (limbRun H n c).1 = [] ∧
    (limbRun H n c).2.2.state = c.state ∧
    (limbRun H n c).2.2.block = c.block ∧
    (limbRun H n c).2.2.index.val ≤ 8 := by
  induction n generalizing c with
  | zero =>
      simp [limbRun]
      omega
  | succ n ih =>
      have hlt : c.index.val < 8 := by omega
      have hneq : c.index.val ≠ 8 := by omega
      let i : Fin 8 := ⟨c.index.val, hlt⟩
      let c' : Cursor := ⟨c.state, c.block, ⟨c.index.val + 1, by omega⟩⟩
      have hr : readRun H c = ([], (word c.block i, c')) := by
        simp [readRun, hneq, i, c']
      simp only [limbRun, hr]
      by_cases hs : masked 31 (word c.block i) = 2147483647
      · simp only [hs]
        have hcidx : c.index.val + 1 + n ≤ 8 := by omega
        have hc' : c'.index.val + n ≤ 8 := by
          change c.index.val + 1 + n ≤ 8
          exact hcidx
        obtain ⟨hcall, hs', hb, hi⟩ := ih c' hc'
        exact ⟨hcall, hs', hb, hi⟩
      · simp only [hs]
        dsimp [c']
        simp
        omega

theorem limbRun_scanAt (H : Bytes → State) (n : Nat) (c : Cursor)
    (h : c.index.val + n ≤ 8) :
    (limbRun H n c).1 = [] ∧
    (limbRun H n c).2.1 = (scanAt c.block c.index.val n h).1 ∧
    (limbRun H n c).2.2.state = c.state ∧
    (limbRun H n c).2.2.block = c.block ∧
    (limbRun H n c).2.2.index.val = c.index.val +
      (scanAt c.block c.index.val n h).2 := by
  induction n generalizing c with
  | zero => simp [limbRun, scanAt, blockSuffix, sourceScan]
  | succ n ih =>
      have hlt : c.index.val < 8 := by omega
      have hneq : c.index.val ≠ 8 := by omega
      let i : Fin 8 := ⟨c.index.val, hlt⟩
      let c' : Cursor := ⟨c.state, c.block, ⟨c.index.val + 1, by omega⟩⟩
      have hr : readRun H c = ([], (word c.block i, c')) := by
        simp [readRun, hneq, i, c']
      simp only [limbRun, hr]
      by_cases hs : masked 31 (word c.block i) = 2147483647
      · simp only [if_pos hs]
        have hcidx : c.index.val + 1 + n ≤ 8 := by omega
        have htail := ih c' (by change c.index.val + 1 + n ≤ 8; exact hcidx)
        have hsuffix : blockSuffix c.block c.index.val (n + 1) h =
            masked 31 (word c.block i) ::
              blockSuffix c.block (c.index.val + 1) n hcidx := rfl
        simp only [scanAt, hsuffix, sourceScan, if_pos hs]
        rcases htail with ⟨hcall, hvalue, hstate, hblock, hindex⟩
        refine ⟨hcall, hvalue, hstate, hblock, ?_⟩
        have hindex' : (limbRun H n c').2.2.index.val = c.index.val + 1 +
            (sourceScan (blockSuffix c.block (c.index.val + 1) n hcidx)).2 := by
          simpa [scanAt, c'] using hindex
        omega
      · simp only [if_neg hs]
        have hcidx : c.index.val + 1 + n ≤ 8 := by omega
        have hsuffix : blockSuffix c.block c.index.val (n + 1) h =
            masked 31 (word c.block i) ::
              blockSuffix c.block (c.index.val + 1) n hcidx := rfl
        simp [scanAt, hsuffix, sourceScan, hs, i, c']

#print axioms limbRun_no_refill
#print axioms limbRun_scanAt
end R444InitialSourceLimb
