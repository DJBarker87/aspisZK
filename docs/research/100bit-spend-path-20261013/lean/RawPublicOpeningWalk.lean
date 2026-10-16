import InitialPublicWalk
import R1StrictReseedDecoder
import R1CarryLast

/-! Public-independent opening-prefix walk. Its base recognizes the strict
reseed frame from the table, extracts its semantic endpoint, and invokes the
public-independent initial walk there. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawPublicOpeningWalk

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

abbrev Payload (L : Nat) := (UnifiedSampler.Public L × State) × List InitialWalk.RawRec

def base (p : Params M Cv L) (T : Table (Addr L) State) (tag : Byte) :
    State → Option (Payload L) := fun endpoint =>
  match StrictReseedDecoder.recover tag T endpoint with
  | none => none
  | some (_, semanticEnd) =>
      (InitialPublicWalk.walk p T 27 semanticEnd).map fun result =>
        (result.1, CarryLast.apply endpoint result.2)

def walk (p : Params M Cv L) (T : Table (Addr L) State) (tag : Byte)
    (fuel : Nat) : State → Option (Payload L)
  | endpoint =>
      match base p T tag endpoint with
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
                          (walk p T tag fuel prev).map fun result =>
                            (result.1, result.2 ++ [⟨prev, absorbed, label, data, endpoint⟩])

def select (p : Params M Cv L) (T : Table (Addr L) State) (tag : Byte)
    (fuel : Nat) (endpoint : State) : Option (UnifiedSampler.Public L) :=
  (walk p T tag fuel endpoint).map fun result => result.1.1

/-- Select from an ordinary input frame by parsing its preceding state, then
walking back through the opening prefix to the strict reseed and initial root. -/
def selectAbsorb (p : Params M Cv L) (T : Table (Addr L) State) (tag : Byte)
    (fuel : Nat) (a : Addr L) : Option (UnifiedSampler.Public L) :=
  (parseAbsorb a).bind fun (endpoint, _, _) => select p T tag fuel endpoint

theorem selectAbsorb_of_current (p : Params M Cv L) (T : Table (Addr L) State)
    (tag : Byte) (fuel : Nat) (a : Addr L) (endpoint : State) (label : Byte) (data : Bytes)
    (pub : UnifiedSampler.Public L) (hparse : parseAbsorb a = some (endpoint, label, data))
    (hselect : select p T tag fuel endpoint = some pub) :
    selectAbsorb p T tag fuel a = some pub := by
  simp [selectAbsorb, hparse, hselect]

theorem base_of_recovered_reseed (p : Params M Cv L) (T : Table (Addr L) State)
    (tag : Byte) (endpoint semanticEnd : State) (r : Addr L)
    (pub : UnifiedSampler.Public L) (c1 : State) (records : List InitialWalk.RawRec)
    (hrec : StrictReseedDecoder.recover tag T endpoint = some (r, semanticEnd))
    (hwalk : InitialPublicWalk.walk p T 27 semanticEnd = some ((pub,c1),records)) :
    base p T tag endpoint = some ((pub,c1),CarryLast.apply endpoint records) := by
  simp [base,hrec,hwalk]

theorem walk_of_lookups (p : Params M Cv L) (T : Table (Addr L) State) (tag : Byte)
    (fuel n : Nat) (s absorbed : Nat → State) (label : Nat → Byte)
    (data : Nat → Bytes) (pub : UnifiedSampler.Public L) (c1 : State)
    (initialRecords : List InitialWalk.RawRec)
    (hle : n ≤ fuel)
    (hadv : ∀ j, j < n → theUnique (advPre p T (s (j + 1))) = some (absorbed j))
    (habs : ∀ j, j < n → ∃ a, ReseedBoundary.findCell T (absorbed j) = some a ∧
      parseAbsorb a = some (s j, label j, data j))
    (hbase : base p T tag (s 0) = some ((pub,c1),initialRecords))
    (hstop : ∀ j, 0 < j → j ≤ n → base p T tag (s j) = none) :
    walk p T tag fuel (s n) =
      some ((pub,c1), initialRecords ++ InitialWalk.records s absorbed label data n) := by
  induction n generalizing fuel with
  | zero =>
      cases fuel with
      | zero => simpa [walk,hbase,InitialWalk.records]
      | succ fuel => simpa [walk,hbase,InitialWalk.records]
  | succ n ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hnone : base p T tag (s (n + 1)) = none :=
            hstop (n + 1) (by omega) (by omega)
          have hlast : n < n + 1 := by omega
          obtain ⟨a,ha,hparse⟩ := habs n hlast
          simp only [walk,hnone,hadv n hlast,ha,hparse]
          have hrec := ih fuel (by omega)
            (fun j hj => hadv j (by omega))
            (fun j hj => habs j (by omega))
            (fun j hj hjle => hstop j hj (by omega))
          rw [hrec]
          simp [InitialWalk.records,List.range_succ,List.map_append,List.map_singleton,
            List.append_assoc]

theorem select_of_lookups (p : Params M Cv L) (T : Table (Addr L) State) (tag : Byte)
    (fuel n : Nat) (s absorbed : Nat → State) (label : Nat → Byte)
    (data : Nat → Bytes) (pub : UnifiedSampler.Public L) (c1 : State)
    (initialRecords : List InitialWalk.RawRec)
    (hle : n ≤ fuel)
    (hadv : ∀ j, j < n → theUnique (advPre p T (s (j + 1))) = some (absorbed j))
    (habs : ∀ j, j < n → ∃ a, ReseedBoundary.findCell T (absorbed j) = some a ∧
      parseAbsorb a = some (s j, label j, data j))
    (hbase : base p T tag (s 0) = some ((pub,c1),initialRecords))
    (hstop : ∀ j, 0 < j → j ≤ n → base p T tag (s j) = none) :
    select p T tag fuel (s n) = some pub := by
  unfold select
  rw [walk_of_lookups p T tag fuel n s absorbed label data pub c1 initialRecords
    hle hadv habs hbase hstop]
  rfl

#print axioms walk_of_lookups
#print axioms base_of_recovered_reseed
#print axioms selectAbsorb_of_current
#print axioms select_of_lookups
end AspisR1.RawPublicOpeningWalk
end
