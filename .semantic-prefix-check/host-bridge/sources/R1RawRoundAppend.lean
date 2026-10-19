import R1RawRoundCompletion

/-! Append and offset bookkeeping for the abstract raw-record decoder. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawRoundAppend

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.InitialWalk

variable {M Cv : Type} {L : Nat}

theorem decode_append (p : Params M Cv L) (j : Nat)
    (left right : List InitialWalk.RawRec)
    (lout rout : List (Rec M))
    (hl : RawRoundDecode.decode p j left = some lout)
    (hr : RawRoundDecode.decode p (j + left.length) right = some rout) :
    RawRoundDecode.decode p j (left ++ right) = some (lout ++ rout) := by
  induction left generalizing j lout with
  | nil =>
      have hout : lout = [] := by simpa [RawRoundDecode.decode] using hl
      subst lout
      simpa [RawRoundDecode.decode] using hr
  | cons q left ih =>
      cases q with
      | mk prev absorbed label data next =>
        by_cases hlabel : label = p.lbl j
        · cases hdata : p.dec data with
          | none => simp [RawRoundDecode.decode, hlabel, hdata] at hl
          | some m =>
            cases htail : RawRoundDecode.decode p (j + 1) left with
            | none => simp [RawRoundDecode.decode, hlabel, hdata, htail] at hl
            | some ltail =>
              have hout : (prev, absorbed, m, next) :: ltail = lout := by
                simpa [RawRoundDecode.decode, hlabel, hdata, htail] using hl
              rw [← hout]
              have hr' : RawRoundDecode.decode p ((j + 1) + left.length) right = some rout := by
                have hlen :
                    (InitialWalk.RawRec.mk prev absorbed label data next :: left).length =
                      left.length + 1 := by simp
                have hidx : j + (left.length + 1) = (j + 1) + left.length := by omega
                rw [hlen, hidx] at hr
                exact hr
              have hrest := ih (j + 1) ltail htail hr'
              simp [RawRoundDecode.decode, hlabel, hdata, hrest]
        · simp [RawRoundDecode.decode, hlabel] at hl

theorem decode_records_offset (p : Params M Cv L) (offset : Nat)
    (s absorbed : Nat → State) (msg : Nat → M) (n : Nat) :
    RawRoundDecode.decode p offset
      (InitialWalk.records s absorbed (fun j => p.lbl (offset + j))
        (fun j => p.enc (msg j)) n) =
      some (RawRoundCompletion.recs s absorbed msg (fun j => s (j + 1)) n) := by
  induction n with
  | zero => simp [InitialWalk.records, RawRoundDecode.decode, RawRoundCompletion.recs]
  | succ n ih =>
      have hrecords :
          InitialWalk.records s absorbed (fun j => p.lbl (offset + j))
            (fun j => p.enc (msg j)) (n + 1) =
          InitialWalk.records s absorbed (fun j => p.lbl (offset + j))
            (fun j => p.enc (msg j)) n ++
            [⟨s n, absorbed n, p.lbl (offset + n), p.enc (msg n), s (n + 1)⟩] := by
        simp [InitialWalk.records, List.range_succ, List.map_append]
      rw [hrecords]
      have hdecode := RawRoundDecode.decode_append_one p offset
        (InitialWalk.records s absorbed (fun j => p.lbl (offset + j))
          (fun j => p.enc (msg j)) n)
        (RawRoundCompletion.recs s absorbed msg (fun j => s (j + 1)) n)
        (s n, absorbed n, msg n, s (n + 1)) ih
      simpa [RawRoundCompletion.recs_length, RawRoundCompletion.recs_succ,
        RawRoundDecode.rawOf, InitialWalk.records, Nat.add_assoc] using hdecode

theorem completeRounds_append_list (p : Params M Cv L)
    (T : Table (Addr L) State) (acc : Addr L → State) (j : Nat)
    (left right : List (Rec M)) :
    completeRounds p T acc j (left ++ right) =
      completeRounds p T acc j left ++
        completeRounds p T acc (j + left.length) right := by
  induction left generalizing j with
  | nil => rfl
  | cons r left ih =>
      simp only [List.cons_append, completeRounds]
      rw [ih (j + 1)]
      simp only [List.length_cons]
      rw [show j + 1 + left.length = j + (left.length + 1) by omega]

#print axioms decode_append
#print axioms decode_records_offset
#print axioms completeRounds_append_list

end AspisR1.RawRoundAppend
end
