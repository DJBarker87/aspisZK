import RawPublicInitParser
import R1InitialWalk

/-! The existing structural prefix walk with a public-independent strict root
parser. Its lookup proof is reused with public/root pairs as terminal data. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InitialPublicWalk

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

abbrev RawRec := InitialWalk.RawRec

def rootAt (T : Table (Addr L) State) (s : State) : Option (UnifiedSampler.Public L × State) :=
  (ReseedBoundary.findCell T s).bind RawPublicInitParser.parse

def walk (p : Params M Cv L) (T : Table (Addr L) State) :
    Nat → State → Option ((UnifiedSampler.Public L × State) × List RawRec)
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
                  match rootAt T prev with
                  | some c1 => some (c1, [record])
                  | none =>
                      (walk p T fuel prev).map
                        fun result => (result.1, result.2 ++ [record])

abbrev records := InitialWalk.records

theorem walk_of_lookups (p : Params M Cv L)
    (T : Table (Addr L) State) (fuel n : Nat)
    (s absorbed : Nat → State) (label : Nat → Byte) (data : Nat → Bytes)
    (pub : UnifiedSampler.Public L) (c1 : State)
    (hn : 0 < n) (hle : n ≤ fuel)
    (hadv : ∀ j, j < n → theUnique (advPre p T (s (j + 1))) = some (absorbed j))
    (habs : ∀ j, j < n → ∃ a, ReseedBoundary.findCell T (absorbed j) = some a ∧
      parseAbsorb a = some (s j, label j, data j))
    (hroot : rootAt T (s 0) = some (pub,c1))
    (hstop : ∀ j, 0 < j → j < n → rootAt T (s j) = none) :
    walk p T fuel (s n) = some ((pub,c1), records s absorbed label data n) := by
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
            simp [records,InitialWalk.records]
          · have hnone : rootAt T (s n) = none :=
              hstop n (by omega) (by omega)
            rw [hnone]
            have hrec := ih fuel (by omega) (by omega)
              (fun j hj => hadv j (by omega))
              (fun j hj => habs j (by omega))
              (fun j hj hjn => hstop j hj (by omega))
            rw [hrec]
            simp [Option.map_some, records,InitialWalk.records, List.range_succ, List.map_append,
              List.map_singleton]

#print axioms walk_of_lookups
end AspisR1.InitialPublicWalk
end
