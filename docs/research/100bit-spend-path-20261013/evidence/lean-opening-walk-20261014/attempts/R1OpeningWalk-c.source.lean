import R1InitialWalk

/-! Structural absorb/advance walk with an abstract base decoder. This module
contains no public-initialization or root-parsing behavior. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OpeningWalk

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

abbrev Base := State → Option (State × List InitialWalk.RawRec)

def walk (p : Params M Cv L) (T : Table (Addr L) State) (base : Base) :
    Nat → State → Option (State × List InitialWalk.RawRec)
  | fuel, endpoint =>
      match base endpoint with
      | some result => some result
      | none =>
          match fuel with
          | 0 => none
          | fuel + 1 =>
              match theUnique (advPre p T endpoint) with
              | none => none
              | some absorbed =>
                  match ReseedBoundary.findCell T absorbed with
                  | none => none
                  | some a =>
                      match parseAbsorb a with
                      | none => none
                      | some (prev, label, data) =>
                          (walk p T base fuel prev).map fun result =>
                            (result.1, result.2 ++
                              [⟨prev, absorbed, label, data, endpoint⟩])

theorem walk_of_lookups (p : Params M Cv L)
    (T : Table (Addr L) State) (base : Base) (fuel n : Nat)
    (s absorbed : Nat → State) (label : Nat → Byte) (data : Nat → Bytes)
    (c1 : State) (pre : List InitialWalk.RawRec)
    (hle : n ≤ fuel)
    (hadv : ∀ j, j < n →
      theUnique (advPre p T (s (j + 1))) = some (absorbed j))
    (habs : ∀ j, j < n →
      ∃ a, ReseedBoundary.findCell T (absorbed j) = some a ∧
        parseAbsorb a = some (s j, label j, data j))
    (hbase : base (s 0) = some (c1, pre))
    (hstop : ∀ j, 0 < j → j ≤ n → base (s j) = none) :
    walk p T base fuel (s n) =
      some (c1, pre ++ InitialWalk.records s absorbed label data n) := by
  induction n generalizing fuel with
  | zero =>
      cases fuel with
      | zero => simpa [walk, hbase, InitialWalk.records]
      | succ fuel => simpa [walk, hbase, InitialWalk.records]
  | succ n ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hnone : base (s (n + 1)) = none :=
            hstop (n + 1) (by omega) (by omega)
          have hlast : n < n + 1 := by omega
          obtain ⟨a, ha, hparse⟩ := habs n hlast
          simp only [walk, hnone, hadv n hlast, ha, hparse]
          have hrec := ih (by omega)
            (fun j hj => hadv j (by omega))
            (fun j hj => habs j (by omega)) hbase
            (fun j hj hjle => hstop j hj (by omega))
          rw [hrec]
          simp [InitialWalk.records, List.range_succ, List.map_append]

#print axioms walk_of_lookups
end AspisR1.OpeningWalk
end
