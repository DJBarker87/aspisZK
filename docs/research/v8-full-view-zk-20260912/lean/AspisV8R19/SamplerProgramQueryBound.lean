import AspisV8R19.QM31SamplerProgram

/-! A compositional query bound for the source-shaped QM31 challenge.

`Within` counts the complete oracle trace of every deterministic branch.  The
bound is deliberately symbolic and preserves all result/error branches; no
freshness, distribution, or source-callback premise is used.
-/
set_option autoImplicit false
namespace AspisV8R19.SamplerProgramQueryBound

open DuplexFrames SourceDuplexStep SourceOraclePrograms SamplerWords
open MemoizedProgramLaw OracleProgramOps
open AspisV8R19.QM31SamplerProgram

def Within {I A O : Type} (n : Nat) (p : Program I A O) : Prop :=
  ∀ H, (eval H p).1.length ≤ n

theorem within_done {I A O : Type} (n : Nat) (o : O) :
    Within n (.done o : Program I A O) := by
  intro H
  simp [eval]

theorem within_ask {I A O : Type} (n : Nat) (i : I)
    (next : A → Program I A O)
    (h : ∀ a, Within n (next a)) :
    Within (n+1) (.ask i next) := by
  intro H
  simp only [Within, eval]
  have ha := h (H i) H
  simp only [List.length_cons]
  omega

theorem within_bind {I A O R : Type} (m n : Nat)
    (p : Program I A O) (next : O → Program I A R)
    (hp : Within m p) (hn : ∀ o, Within n (next o)) :
    Within (m+n) (bind p next) := by
  intro H
  rw [eval_bind]
  simp only [List.length_append]
  have h1 := hp H
  have h2 := hn ((eval H p).2) H
  omega

theorem squeezeProgram_within (s : State) :
    Within 2 (squeezeProgram s) := by
  exact within_ask 1 _ _
    (fun _ => within_ask 0 _ _ (fun _ => within_done 0 _))

theorem readProgram_within (c : Cursor) :
    Within 2 (readProgram c) := by
  by_cases h : c.index.val = 8
  · simp only [readProgram, h]
    exact within_bind 2 0 (squeezeProgram c.state)
      (fun _ => .done _) (squeezeProgram_within c.state)
      (fun _ => within_done 0 _)
  · simp only [readProgram, h]
    exact within_done 2 _

theorem limbProgram_within (n : Nat) (c : Cursor) :
    Within (2*n) (limbProgram n c) := by
  induction n generalizing c with
  | zero => exact within_done 0 _
  | succ n ih =>
      have hb : Within (2 + 2*n) (limbProgram (n+1) c) := by
        apply within_bind 2 (2*n) (readProgram c)
          (fun r => if masked 31 r.1 = 2147483647 then
            limbProgram n r.2 else .done (some (masked 31 r.1),r.2))
          (readProgram_within c)
        intro r
        split
        · exact ih r.2
        · exact within_done (2*n) _
      simpa [Nat.mul_succ, Nat.add_comm] using hb

theorem limbsProgram_within (n : Nat) (c : Cursor) :
    Within (16*n) (limbsProgram n c) := by
  induction n generalizing c with
  | zero => exact within_done 0 _
  | succ n ih =>
      have hb : Within (16 + 16*n) (limbsProgram (n+1) c) := by
        apply within_bind (16) (16*n) (limbProgram 8 c)
          (fun r => match r.1 with
            | none => .done (none,r.2)
            | some a => bind (limbsProgram n r.2)
                (fun tail => .done (tail.1.map (a::·),tail.2)))
          (by simpa using limbProgram_within 8 c)
        intro r
        cases r.1 with
        | none => exact within_done (16*n) _
        | some a =>
            exact within_bind (16*n) 0 (limbsProgram n r.2)
              (fun tail => .done (tail.1.map (a::·),tail.2))
              (ih r.2) (fun _ => within_done 0 _)
      simpa [Nat.mul_succ, Nat.add_comm] using hb

theorem challengeProgram_within (s : State) :
    Within 66 (challengeProgram s) := by
  simp only [challengeProgram]
  apply within_bind 2 64 (squeezeProgram s)
    (fun p => bind (limbsProgram 4 ⟨p.2,p.1,0⟩)
      (fun r => .done (r.1,r.2.state)))
    (squeezeProgram_within s)
  intro p
  apply within_bind 64 0 (limbsProgram 4 ⟨p.2,p.1,0⟩)
    (fun r => .done (r.1,r.2.state))
    (by simpa using limbsProgram_within 4 ⟨p.2,p.1,0⟩)
  intro r
  exact within_done 0 _

#print axioms within_bind
#print axioms readProgram_within
#print axioms limbProgram_within
#print axioms limbsProgram_within
#print axioms challengeProgram_within
end AspisV8R19.SamplerProgramQueryBound
