import R1RawRoundDecode
import R1CarryLast

/-! Connect explicit records to the abstract record decoder and completing
sampler. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawRoundCompletion

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.InitialWalk

variable {M Cv : Type} {L : Nat}

def recs (s absorbed : Nat → State) (msg : Nat → M)
    (next : Nat → State) (n : Nat) : List (Rec M) :=
  (List.range n).map fun j => (s j, absorbed j, msg j, next j)

theorem recs_length (s absorbed : Nat → State) (msg : Nat → M)
    (next : Nat → State) (n : Nat) : (recs s absorbed msg next n).length = n := by
  simp [recs]

theorem recs_succ (s absorbed : Nat → State) (msg : Nat → M)
    (next : Nat → State) (n : Nat) :
    recs s absorbed msg next (n + 1) =
      recs s absorbed msg next n ++ [(s n, absorbed n, msg n, next n)] := by
  simp [recs, List.range_succ, List.map_append]

theorem decode_records (p : Params M Cv L) (s absorbed : Nat → State)
    (msg : Nat → M) (n : Nat) :
    RawRoundDecode.decode p 0
      (InitialWalk.records s absorbed p.lbl (fun j => p.enc (msg j)) n) =
      some (recs s absorbed msg (fun j => s (j + 1)) n) := by
  induction n with
  | zero => simp [InitialWalk.records, recs, RawRoundDecode.decode]
  | succ n ih =>
      have hrecords : InitialWalk.records s absorbed p.lbl (fun j => p.enc (msg j)) (n + 1) =
          InitialWalk.records s absorbed p.lbl (fun j => p.enc (msg j)) n ++
            [⟨s n, absorbed n, p.lbl n, p.enc (msg n), s (n + 1)⟩] := by
        simp [InitialWalk.records, List.range_succ, List.map_append]
      rw [hrecords]
      have hdecode := RawRoundDecode.decode_append_one p 0
        (InitialWalk.records s absorbed p.lbl (fun j => p.enc (msg j)) n)
        (recs s absorbed msg (fun j => s (j + 1)) n)
        (s n, absorbed n, msg n, s (n + 1)) ih
      simpa [recs_length, recs_succ, RawRoundDecode.rawOf, InitialWalk.records] using hdecode

theorem decode_carried_records_succ (p : Params M Cv L)
    (s absorbed : Nat → State) (msg : Nat → M) (n : Nat) (endpoint : State) :
    RawRoundDecode.decode p 0
      (CarryLast.apply endpoint
        (InitialWalk.records s absorbed p.lbl (fun j => p.enc (msg j)) (n + 1))) =
      some (recs s absorbed msg (fun j => s (j + 1)) n ++
        [(s n, absorbed n, msg n, endpoint)]) := by
  rw [CarryLast.records_succ]
  have hdecode := RawRoundDecode.decode_append_one p 0
    (InitialWalk.records s absorbed p.lbl (fun j => p.enc (msg j)) n)
    (recs s absorbed msg (fun j => s (j + 1)) n)
    (s n, absorbed n, msg n, endpoint) (decode_records p s absorbed msg n)
  simpa [recs_length, RawRoundDecode.rawOf, InitialWalk.records] using hdecode

theorem complete_recs (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (offset : Nat) (s absorbed : Nat → State)
    (msg : Nat → M) (next : Nat → State) : ∀ n,
    completeRounds p T acc offset (recs s absorbed msg next n) =
      (List.range n).map (fun j =>
        (msg j, (p.σ (offset + j)
          ((T (squeezeA p (absorbed j))).getD (acc (squeezeA p (absorbed j)))), next j))) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [recs_succ]
      rw [completeRounds_append]
      rw [ih]
      simp [List.range_succ, List.map_append, Nat.add_assoc, recs]

#print axioms recs_length
#print axioms recs_succ
#print axioms decode_records
#print axioms decode_carried_records_succ
#print axioms complete_recs

end AspisR1.RawRoundCompletion
end
