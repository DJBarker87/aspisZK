import R1DuplexAbsorb

/-! A bounded table search finds an absorb boundary without knowing how
many advance edges lead back to it. Collision and table premises are
supplied by the existing duplex trace lemmas, not by a guessed boundary. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DuplexSeek
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

def seek (p : Params M Cv L) (T : Table (Addr L) State) :
    Nat → State → Option (Addr L × List State)
  | 0, _ => none
  | fuel + 1, s =>
      match theUnique (absCells T s) with
      | some a => some (a, [s])
      | none =>
          match theUnique (advPre p T s) with
          | none => none
          | some prev => (seek p T fuel prev).map (fun r => (r.1, r.2 ++ [s]))

theorem seek_of_spine (p : Params M Cv L) (T : Table (Addr L) State)
    (s : Nat → State) (a : Addr L) (n fuel : Nat)
    (hroot : theUnique (absCells T (s 0)) = some a)
    (hnone : ∀ j < n, absCells T (s (j + 1)) = ∅)
    (hpre : ∀ j < n, theUnique (advPre p T (s (j + 1))) = some (s j))
    (hfuel : n + 1 ≤ fuel) :
    seek p T fuel (s n) = some (a, (List.range (n + 1)).map s) := by
  induction n generalizing fuel with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel => simp only [seek, hroot, List.range_one, List.map_cons, List.map_nil]
  | succ n ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hn : theUnique (absCells T (s (n + 1))) = none := by
            rw [hnone n (by omega)]
            exact DuplexAbsorb.theUnique_empty
          simp only [seek, hn, hpre n (by omega)]
          rw [ih fuel (fun j hj => hnone j (by omega))
            (fun j hj => hpre j (by omega)) (by omega)]
          simp only [Option.map_some, List.range_succ, List.map_append,
            List.map_singleton, List.append_assoc]

#print axioms seek_of_spine
end AspisR1.DuplexSeek
end
