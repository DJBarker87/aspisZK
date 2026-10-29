import R1Z.ProverCommitSourceFailure

/-! Exact finite decoder/cursor failure classification. No source caller
identity is assumed by this module. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCursor
open R1Z.CommitReadsR1 R1Z.ProverCommitSequentialFibres
  R1Z.ProverCommitWordCarrier

def runFrom {N : Nat} (ws : Fin N → Word) (p : Nat) : Nat → Option Nat
  | 0 => some p
  | L+1 => (tryLimb ws p 16).bind (fun q => runFrom ws q L)

theorem runFrom_succ {N : Nat} (ws : Fin N → Word) (L p : Nat) :
    runFrom ws p (L+1) = (runFrom ws p L).bind (fun q => tryLimb ws q 16) := by
  induction L generalizing p with
  | zero => cases ht : tryLimb ws p 16 <;> simp [runFrom, ht]
  | succ L ih =>
    change (tryLimb ws p 16).bind (fun q => runFrom ws q (L+1)) =
      ((tryLimb ws p 16).bind (fun q => runFrom ws q L)).bind (fun q => tryLimb ws q 16)
    rw [Option.bind_assoc]
    congr 1
    funext q
    exact ih q

theorem runFrom_zero {N : Nat} (ws : Fin N → Word) (L : Nat) :
    runFrom ws 0 L = limbPos ws L := by
  induction L with
  | zero => rfl
  | succ L ih => rw [runFrom_succ, ih]; rfl

def cursor {N : Nat} (ws : Fin N → Word) (p L r : Nat) : Option Nat :=
  match L with
  | 0 => some p
  | L+1 => (tryLimb ws p r).bind (fun q => runFrom ws q L)

theorem cursor_step {N : Nat} (ws : Fin N → Word) (p L r : Nat) :
    cursor ws p (L+1) (r+1) =
      if rejB (getW ws p) = true then cursor ws (p+1) (L+1) r
      else cursor ws (p+1) L 16 := by
  change ((if rejB (getW ws p) = true then tryLimb ws (p+1) r else some (p+1)).bind (fun q => runFrom ws q L)) = _
  split
  · rfl
  · cases L <;> rfl

variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem decoder_cursor {N : Nat} (ws : Fin N → Word)
    (n L r p : Nat) (tail : Fin n → Word)
    (hword : ∀ i, tail i = getW ws (p+i.val))
    (hbudget : L ≠ 0 → 16*(L-1)+r ≤ n) :
    decodeWords (accepted (K := K)) n L r tail = none ↔ cursor ws p L r = none := by
  induction n generalizing L r p with
  | zero =>
    cases L with
    | zero => simp [decodeWords, cursor]
    | succ L =>
      have hb := hbudget (by omega)
      have hr : r = 0 := by omega
      subst r
      simp [decodeWords, cursor, tryLimb]
  | succ n ih =>
    cases L with
    | zero => simp [decodeWords, cursor]
    | succ L =>
      cases r with
      | zero => simp [decodeWords, cursor, tryLimb]
      | succ r =>
        have hw : tail 0 = getW ws p := by simpa using hword 0
        have ht : ∀ i : Fin n, tail i.succ = getW ws (p+1+i.val) := by
          intro i
          simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using hword i.succ
        have hb := hbudget (by omega)
        have hmore := ih (L+1) r (p+1) (fun i => tail i.succ) ht (by intro _; omega)
        have hless := ih L 16 (p+1) (fun i => tail i.succ) ht (by intro h; omega)
        rw [cursor_step]
        cases hd : accepted (K := K) (tail 0) with
        | none =>
          have hj : rejB (getW ws p) = true := by
            rw [← hw]; exact (accepted_failure (K := K) (tail 0)).mp hd
          simpa only [decodeWords, step, hd, if_pos hj] using hmore
        | some a =>
          have hj : ¬ rejB (getW ws p) = true := by
            intro h
            have hf := (accepted_failure (K := K) (tail 0)).mpr (show rejB (tail 0) = true by rwa [hw])
            rw [hd] at hf
            contradiction
          simp only [decodeWords, step, hd, if_neg hj]
          cases hv : decodeWords (accepted (K := K)) n L 16 (fun i => tail i.succ) with
          | none => exact ⟨fun _ => hless.mp hv, fun _ => rfl⟩
          | some v =>
            constructor
            · intro h; cases h
            · intro h
              have hf := hless.mpr h
              rw [hv] at hf
              contradiction

theorem decoder_exhausted {N : Nat} (ws : Fin N → Word) (L : Nat)
    (hbudget : 16*L ≤ N) :
    arrayDecode (accepted (K := K)) N L 16 ws = none ↔ Exhausted ws L := by
  have h := decoder_cursor (K := K) ws N L 16 0 ws
    (by intro i; simp [getW, i.isLt]) (by intro h; omega)
  have hc : cursor ws 0 L 16 = limbPos ws L := by
    cases L with
    | zero => rfl
    | succ L => exact runFrom_zero ws (L+1)
  simpa only [arrayDecode, Option.map_eq_none_iff, hc, Exhausted] using h

#print axioms runFrom_succ
#print axioms runFrom_zero
#print axioms cursor_step
#print axioms decoder_cursor
#print axioms decoder_exhausted
end R1Z.ProverCommitCursor
