import AspisV8R19.IndependentMeanFixedTape
import AspisV8R19.QM31SamplerProgram

/-! Structural fixed-tape certificates for the source-shaped QM31 challenge.

These declarations only count branches of the already-defined `Program`s.
They preserve all retry and error branches and make no statement about source
equivalence, freshness, distribution, or security. -/
set_option autoImplicit false
namespace AspisV8R19.IndependentMeanFixedTapeQM31

open DuplexFrames SourceDuplexStep SourceOraclePrograms SamplerWords
open MemoizedProgramLaw OracleProgramOps
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.IndependentMeanFixedTape

variable {I A O : Type}

def pad {p : Program I A O} {n : Nat} :
    Within p n → (k : Nat) → Within p (n + k)
  | .done o n, k => .done o (n + k)
  | .ask i next n h, k => by
      have branches : ∀ a, Within (next a) (n + k) :=
        fun a => pad (h a) k
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Within.ask i next (n + k) branches)

def withinBind {I A O R : Type} (m n : Nat)
    (p : Program I A O) (next : O → Program I A R)
    (hp : Within p m) (hn : ∀ o, Within (next o) n) :
    Within (OracleProgramOps.bind p next) (m + n) :=
  match hp with
  | .done o m => by
      simpa [OracleProgramOps.bind, Nat.add_comm] using pad (hn o) m
  | .ask i k m h => by
      have branches : ∀ a,
          Within (OracleProgramOps.bind (k a) next) (m + n) :=
        fun a => withinBind m n (k a) next (h a) hn
      have hask := Within.ask i (fun a => OracleProgramOps.bind (k a) next)
        (m + n) branches
      simpa [OracleProgramOps.bind, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hask

def squeezeProgram_within (s : State) :
    Within (squeezeProgram s) 2 := by
  exact Within.ask _ _ 1 (fun _ =>
    Within.ask _ _ 0 (fun _ => Within.done _ 0))

def readProgram_within (c : Cursor) :
    Within (readProgram c) 2 := by
  by_cases h : c.index.val = 8
  · simp only [readProgram, h]
    apply withinBind 2 0 (squeezeProgram c.state)
    · exact squeezeProgram_within c.state
    · intro p
      exact Within.done _ 0
  · simp only [readProgram, h]
    exact Within.done _ 2

def limbProgram_within (n : Nat) (c : Cursor) :
    Within (limbProgram n c) (2 * n) := by
  induction n generalizing c with
  | zero => exact Within.done _ 0
  | succ n ih =>
      have hlimb := withinBind 2 (2 * n) (readProgram c)
        (fun r => if masked 31 r.1 = 2147483647 then
          limbProgram n r.2
        else .done (some (masked 31 r.1), r.2))
        (readProgram_within c)
        (fun r => by
          split
          · exact ih r.2
          · exact Within.done _ (2 * n))
      simpa [limbProgram, Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hlimb

def limbsProgram_within (n : Nat) (c : Cursor) :
    Within (limbsProgram n c) (16 * n) := by
  induction n generalizing c with
  | zero => exact Within.done _ 0
  | succ n ih =>
      have hlimbs := withinBind 16 (16 * n) (limbProgram 8 c)
        (fun r => match r.1 with
          | none => .done (none, r.2)
          | some a => OracleProgramOps.bind (limbsProgram n r.2)
              (fun tail => .done (tail.1.map (a :: ·), tail.2)))
        (by simpa using limbProgram_within 8 c)
        (fun r => by
          cases r.1 with
          | none => exact Within.done _ (16 * n)
          | some a =>
              exact withinBind (16 * n) 0 (limbsProgram n r.2)
                (fun tail => .done (tail.1.map (a :: ·), tail.2))
                (ih r.2) (fun _ => Within.done _ 0))
      change Within (OracleProgramOps.bind (limbProgram 8 c) (fun r =>
        match r.1 with
        | none => .done (none, r.2)
        | some a => OracleProgramOps.bind (limbsProgram n r.2)
            (fun tail => .done (tail.1.map (a :: ·), tail.2))))
        (16 * (n + 1))
      rw [show 16 * (n + 1) = 16 + 16 * n by omega]
      exact hlimbs

def challengeProgram_within (s : State) :
    Within (challengeProgram s) 66 := by
  simp only [challengeProgram]
  apply withinBind 2 64 (squeezeProgram s)
  · exact squeezeProgram_within s
  · intro p
    apply withinBind 64 0 (limbsProgram 4 ⟨p.2, p.1, 0⟩)
    · simpa using limbsProgram_within 4 ⟨p.2, p.1, 0⟩
    · intro r
      exact Within.done _ 0

#print axioms challengeProgram_within

end AspisV8R19.IndependentMeanFixedTapeQM31
