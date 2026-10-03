import AspisV8R19.QM31SamplerProgram

set_option autoImplicit false
namespace R444InitialSourceLimb
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SamplerWords

/-- Source-aligned words in the current block, beginning at a cursor index.
The caller supplies the bound that keeps every accessed index in Fin 8. -/
def blockSuffix (block : State) (i : Fin 8) : (n : Nat) → i.val + n ≤ 8 → List Nat
  | 0, _ => []
  | n + 1, h =>
      masked 31 (word block i) ::
        blockSuffix block ⟨i.val + 1, by have hi := i.isLt; omega⟩ n (by omega)

def sourceScan : List Nat → Option Nat × Nat
  | [] => (none, 0)
  | w :: ws =>
      if masked 31 w = 2147483647 then
        let tail := sourceScan ws
        (tail.1, tail.2 + 1)
      else (some (masked 31 w), 1)

def scanAt (block : State) (i : Fin 8) (n : Nat) (h : i.val + n ≤ 8) : Option Nat × Nat :=
  sourceScan (blockSuffix block i n h)

theorem limbRun_no_refill (H : Bytes → State) (n : Nat) (c : Cursor)
    (h : c.index.val + n ≤ 8) :
    (limbRun H n c).1 = [] ∧
    (limbRun H n c).2.2.state = c.state ∧
    (limbRun H n c).2.2.block = c.block ∧
    (limbRun H n c).2.2.index.val ≤ 8 := by
  induction n generalizing c with
  | zero => simp [limbRun]
  | succ n ih =>
      have hlt : c.index.val < 8 := by omega
      have hneq : c.index.val ≠ 8 := by omega
      let i : Fin 8 := ⟨c.index.val, hlt⟩
      have hr : readRun H c =
          ([], (word c.block i,
            { state := c.state, block := c.block,
              index := ⟨c.index.val + 1, by omega⟩ })) := by
        simp [readRun, hneq, i]
      simp only [limbRun, hr]
      split
      · rename_i hreject
        obtain ⟨hcall, hs, hb, hi⟩ := ih
          ({ state := c.state, block := c.block,
             index := ⟨c.index.val + 1, by omega⟩ }) (by omega)
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact hcall
        · exact hs
        · exact hb
        · simpa using hi
      · refine ⟨rfl, rfl, rfl, ?_⟩
        simp
        omega

theorem limbRun_scanAt (H : Bytes → State) (n : Nat) (c : Cursor)
    (h : c.index.val + n ≤ 8) :
    (limbRun H n c).1 = [] ∧
    (limbRun H n c).2.1 = (scanAt c.block ⟨c.index.val, by omega⟩ n h).1 ∧
    (limbRun H n c).2.2.state = c.state ∧
    (limbRun H n c).2.2.block = c.block ∧
    (limbRun H n c).2.2.index.val = c.index.val +
      (scanAt c.block ⟨c.index.val, by omega⟩ n h).2 := by
  induction n generalizing c with
  | zero => simp [limbRun, scanAt, blockSuffix, sourceScan]
  | succ n ih =>
      have hlt : c.index.val < 8 := by omega
      have hneq : c.index.val ≠ 8 := by omega
      let i : Fin 8 := ⟨c.index.val, hlt⟩
      let c' : Cursor := { state := c.state, block := c.block,
        index := ⟨c.index.val + 1, by omega⟩ }
      have hr : readRun H c = ([], (word c.block i, c')) := by
        simp [readRun, hneq, i, c']
      simp only [limbRun, hr]
      by_cases hs : masked 31 (word c.block i) = 2147483647
      · have htail := ih c' (by omega)
        have hwords : blockSuffix c.block i (n + 1) h =
            masked 31 (word c.block i) ::
              blockSuffix c.block ⟨c.index.val + 1, by omega⟩ n (by omega) := rfl
        simp only [scanAt, hwords, sourceScan, hs]
        rcases htail with ⟨hcalls, hval, hstate, hblock, hindex⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact hcalls
        · exact hval
        · exact hstate
        · exact hblock
        · dsimp [c'] at hindex
          simp at hindex
          omega
      · simp only [hs]
        refine ⟨rfl, ?_, rfl, rfl, ?_⟩
        · rfl
        · simp [sourceScan, hs]
          omega

#print axioms limbRun_no_refill
#print axioms limbRun_scanAt
end R444InitialSourceLimb
