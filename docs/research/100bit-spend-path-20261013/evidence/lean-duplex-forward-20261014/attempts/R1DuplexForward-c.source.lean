import FS2.DuplexDecode

/-! Forward reconstruction of a state path from the table's advance cells. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DuplexForward

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def follow (p : Params M Cv L) (T : Table (Addr L) State) :
    Nat → State → Option (List State)
  | 0, s => some [s]
  | n + 1, s =>
      match T (advanceA p s) with
      | none => none
      | some next => (follow p T n next).map (s :: ·)

theorem follow_of_cells (p : Params M Cv L) (T : Table (Addr L) State)
    (s : Nat → State) (n : Nat)
    (hcells : ∀ j < n, T (advanceA p (s j)) = some (s (j + 1))) :
    follow p T n (s 0) = some ((List.range (n + 1)).map s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have hshift : ∀ j < n,
          T (advanceA p (s (j + 1))) = some (s (j + 1 + 1)) := by
        intro j hj
        rw [Nat.add_assoc]
        exact hcells (j + 1) (by omega)
      have ih' := ih (fun j => s (j + 1)) hshift
      simp only [follow, hcells 0 (by omega), Option.map_some, ih']
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
        Function.comp]

theorem follow_length (p : Params M Cv L) (T : Table (Addr L) State)
    (n : Nat) (s : State) (xs : List State)
    (h : follow p T n s = some xs) : xs.length = n + 1 := by
  induction n generalizing s xs with
  | zero =>
      simp only [follow, Option.some.injEq] at h
      subst xs
      rfl
  | succ n ih =>
      simp only [follow] at h
      cases hnext : T (advanceA p s) with
      | none => simp [hnext] at h
      | some next =>
          simp only [hnext, Option.map_some] at h
          cases hrec : follow p T n next with
          | none => simp [hrec] at h
          | some ys =>
              have hx : s :: ys = xs := by simpa [hrec] using h
              subst xs
              simp only [List.length_cons]
              have hlen := ih next ys hrec
              omega

#print axioms follow_of_cells
#print axioms follow_length

end AspisR1.DuplexForward
end
