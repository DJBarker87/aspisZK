import R1ReseedBoundary
import R1PublicInitParse

/-! Structural decoder from a final state back to the fixed public/C1 prefix.
All table and trace facts needed to instantiate the lookup premises remain
explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InitialWalk

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

structure RawRec where
  prev : State
  absorbed : State
  label : Byte
  data : Bytes
  next : State

def rootAt (pubBytes : Bytes) (T : Table (Addr L) State) (s : State) :
    Option State :=
  match ReseedBoundary.findCell T s with
  | none => none
  | some a => PublicInitParse.parse pubBytes a

def walk (p : Params M Cv L) (pubBytes : Bytes) (T : Table (Addr L) State) :
    Nat → State → Option (State × List RawRec)
  | 0, _ => none
  | fuel + 1, endpoint =>
      match theUnique (advPre p T endpoint) with
      | none => none
      | some absorbed =>
          match ReseedBoundary.findCell T absorbed with
          | none => none
          | some a =>
              match parseAbsorb a with
              | none => none
              | some (prev, label, data) =>
                  let record : RawRec := ⟨prev, absorbed, label, data, endpoint⟩
                  match rootAt pubBytes T prev with
                  | some c1 => some (c1, [record])
                  | none =>
                      (walk p pubBytes T fuel prev).map
                        fun result => (result.1, result.2 ++ [record])

def records (s absorbed : Nat → State) (label : Nat → Byte)
    (data : Nat → Bytes) (n : Nat) : List RawRec :=
  (List.range n).map fun j =>
    ⟨s j, absorbed j, label j, data j, s (j + 1)⟩

theorem walk_of_lookups (p : Params M Cv L) (pubBytes : Bytes)
    (T : Table (Addr L) State) (fuel n : Nat)
    (s absorbed : Nat → State) (label : Nat → Byte) (data : Nat → Bytes)
    (c1 : State)
    (hn : 0 < n) (hle : n ≤ fuel)
    (hadv : ∀ j, j < n → theUnique (advPre p T (s (j + 1))) = some (absorbed j))
    (habs : ∀ j, j < n → ∃ a, ReseedBoundary.findCell T (absorbed j) = some a ∧
      parseAbsorb a = some (s j, label j, data j))
    (hroot : rootAt pubBytes T (s 0) = some c1)
    (hstop : ∀ j, 0 < j → j < n → rootAt pubBytes T (s j) = none) :
    walk p pubBytes T fuel (s n) = some (c1, records s absorbed label data n) := by
  induction n generalizing fuel with
  | zero => omega
  | succ n ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hlast : n < n + 1 := by omega
          obtain ⟨a, ha, hparse⟩ := habs n hlast
          simp only [walk, hadv n hlast, ha, hparse]
          by_cases hn0 : n = 0
          · subst n
            rw [hroot]
            simp [records]
          · have hnone : rootAt pubBytes T (s n) = none :=
              hstop n (by omega) (by omega)
            rw [hnone]
            have hrec := ih fuel (by omega) (by omega)
              (fun j hj => hadv j (by omega))
              (fun j hj => habs j (by omega))
              (fun j hj hjn => hstop j hj (by omega))
            rw [hrec]
            simp [Option.map_some, records, List.range_succ, List.map_append,
              List.map_singleton]

#print axioms walk_of_lookups
end AspisR1.InitialWalk
end
