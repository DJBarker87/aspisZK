import R1OpeningPrefixTrace
import R1RawRoundAppend
import R1PrefixAnswers

/-! Pass the recovered two-part raw prefix through the indexed message codec
and the existing round-completion function. Params remains an abstract codec;
its byte-level R1 source instance is not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OpeningPrefixCompletion
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

def typed (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (T : Table (Addr L) State) (semanticFuel openingFuel : Nat) (endpoint : State) :
    Option (State × List (Rec M)) :=
  (OpeningWalk.walk p T (ReseedPrefix.decode p pubBytes tag T semanticFuel)
    openingFuel endpoint).bind fun result =>
      (RawRoundDecode.decode p 0 result.2).map fun rs => (result.1, rs)

def completed (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (T : Table (Addr L) State) (semanticFuel openingFuel : Nat) (endpoint : State)
    (answers : List State) : Option (State × List (M × Chal Cv)) :=
  (typed p pubBytes tag T semanticFuel openingFuel endpoint).map fun result =>
    (result.1, PrefixAnswers.fromAnswers p T 0 result.2 answers)

theorem typed_of_walk (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (T : Table (Addr L) State) (semanticFuel openingFuel : Nat) (endpoint c1 : State)
    (ss sb : Nat → State) (sm : Nat → M) (n : Nat)
    (os ob : Nat → State) (om : Nat → M) (k : Nat)
    (hwalk : OpeningWalk.walk p T (ReseedPrefix.decode p pubBytes tag T semanticFuel)
      openingFuel endpoint = some (c1,
        CarryLast.apply (os 0)
          (InitialWalk.records ss sb p.lbl (fun j => p.enc (sm j)) (n + 1)) ++
        InitialWalk.records os ob (fun j => p.lbl (n + 1 + j))
          (fun j => p.enc (om j)) k)) :
    typed p pubBytes tag T semanticFuel openingFuel endpoint = some (c1,
      (RawRoundCompletion.recs ss sb sm (fun j => ss (j + 1)) n ++
        [(ss n, sb n, sm n, os 0)]) ++
      RawRoundCompletion.recs os ob om (fun j => os (j + 1)) k) := by
  have hs := RawRoundCompletion.decode_carried_records_succ p ss sb sm n (os 0)
  have ho := RawRoundAppend.decode_records_offset p (n + 1) os ob om k
  have hlen : (CarryLast.apply (os 0)
      (InitialWalk.records ss sb p.lbl (fun j => p.enc (sm j)) (n + 1))).length = n + 1 := by
    rw [CarryLast.length_apply]
    simp [InitialWalk.records]
  have hdecode := RawRoundAppend.decode_append p 0 _ _ _ _ hs
    (by simpa only [hlen, Nat.zero_add] using ho)
  simp only [typed, hwalk, Option.bind_some, hdecode, Option.map_some]

theorem completed_of_typed (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (T : Table (Addr L) State) (semanticFuel openingFuel : Nat) (endpoint c1 : State)
    (rs : List (Rec M)) (H : Addr L → State)
    (hT : ∀ a v, T a = some v → v = H a)
    (htyped : typed p pubBytes tag T semanticFuel openingFuel endpoint = some (c1, rs)) :
    completed p pubBytes tag T semanticFuel openingFuel endpoint
      ((PrefixAnswers.missing p T rs).map H) =
      some (c1, completeRounds p emptyTable H 0 rs) := by
  simp only [completed, htyped, Option.map_some, PrefixAnswers.fromAnswers_map p T 0 rs H hT]

theorem completed_rounds (p : Params M Cv L) (H : Addr L → State)
    (ss sb : Nat → State) (sm : Nat → M) (n : Nat)
    (os ob : Nat → State) (om : Nat → M) (k : Nat) :
    completeRounds p emptyTable H 0
      ((RawRoundCompletion.recs ss sb sm (fun j => ss (j + 1)) n ++
          [(ss n, sb n, sm n, os 0)]) ++
        RawRoundCompletion.recs os ob om (fun j => os (j + 1)) k) =
      (((List.range n).map fun j =>
        (sm j, (p.σ j (H (squeezeA p (sb j))), ss (j + 1)))) ++
        [(sm n, (p.σ n (H (squeezeA p (sb n))), os 0))]) ++
      ((List.range k).map fun j =>
        (om j, (p.σ (n + 1 + j) (H (squeezeA p (ob j))), os (j + 1)))) := by
  rw [RawRoundAppend.completeRounds_append_list, completeRounds_append]
  rw [RawRoundCompletion.complete_recs, RawRoundCompletion.complete_recs]
  simp only [List.length_append, List.length_singleton, RawRoundCompletion.recs_length,
    Nat.zero_add, emptyTable, Option.getD_none]

#print axioms typed_of_walk
#print axioms completed_of_typed
#print axioms completed_rounds
end AspisR1.OpeningPrefixCompletion
end
