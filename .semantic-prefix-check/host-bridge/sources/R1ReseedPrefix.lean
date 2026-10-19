import R1InitialWalkCells
import R1DuplexRecordAnchor
import R1StrictReseedTrace
import R1CarryLast

/-! Recover the semantic prefix across the strict opening-domain frame.
The last raw semantic record still stores its ordinary advance output;
the completed-round view replaces only that carried state by the reseed output. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ReseedPrefix
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

def raw (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (T : Table (Addr L) State) (fuel : Nat) (endpoint : State) :
    Option (State × List InitialWalk.RawRec) :=
  match StrictReseedDecoder.recover tag T endpoint with
  | none => none
  | some (_, semanticEnd) => InitialWalk.walk p pubBytes T fuel semanticEnd

def decode (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (T : Table (Addr L) State) (fuel : Nat) (endpoint : State) :
    Option (State × List InitialWalk.RawRec) :=
  (raw p pubBytes tag T fuel endpoint).map fun result =>
    (result.1, CarryLast.apply endpoint result.2)

theorem decode_of_raw (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (T : Table (Addr L) State) (fuel : Nat) (endpoint c1 : State)
    (rs : List InitialWalk.RawRec)
    (h : raw p pubBytes tag T fuel endpoint = some (c1, rs)) :
    decode p pubBytes tag T fuel endpoint = some (c1, CarryLast.apply endpoint rs) := by
  simp only [decode, h, Option.map_some]

theorem raw_before_next (p : Params M Cv L)
    (pubBytes : Bytes) (hlen : pubBytes.length < 2^32)
    (hL : 75 + pubBytes.length ≤ L) (c1 : State) (tag : Byte) (h62 : 62 ≤ L)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable tr)
    (fuel n : Nat) (hn : 0 < n) (hle : n ≤ fuel)
    (s absorbed : Nat → State) (label : Nat → Byte) (data : Nat → Bytes)
    (hD : ∀ j, (data j).length ≤ p.D)
    (hroot : s 0 = H (PublicInitFrame.addr pubBytes hL c1))
    (hi : Read tr (PublicInitFrame.addr pubBytes hL c1))
    (habs : ∀ j < n, absorbed j = H (absorbA p (s j) (label j) (data j) (hD j)))
    (hstep : ∀ j < n, s (j + 1) = H (advanceA p (absorbed j)))
    (har : ∀ j < n, Read tr (absorbA p (s j) (label j) (data j) (hD j)))
    (hdr : ∀ j < n, Read tr (advanceA p (absorbed j)))
    (hr : Read tr (OpeningReseedFrame.addr tag h62 (s n)))
    (c : Addr L) (hc : Read tr c)
    (hp : c.toBytes.take 32 = bytes (H (OpeningReseedFrame.addr tag h62 (s n)))) :
    raw p pubBytes tag (tableBefore emptyTable tr c) fuel
      (H (OpeningReseedFrame.addr tag h62 (s n))) =
      some (c1, InitialWalk.records s absorbed label data n) := by
  let last := advanceA p (absorbed (n - 1))
  let T := tableBefore emptyTable tr c
  have hs : s n = H last := by
    simpa only [last, Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      hstep (n - 1) (by omega)
  have hr' : Read tr (OpeningReseedFrame.addr tag h62 (H last)) := by
    simpa only [hs] using hr
  have hp' : c.toBytes.take 32 = bytes (H (OpeningReseedFrame.addr tag h62 (H last))) := by
    simpa only [hs] using hp
  obtain ⟨hlastr, hrc, _, hrecover⟩ := StrictReseedTrace.recover_before_next p tag h62
    H tr Qtot hcons hQ hold htail last c (hdr (n - 1) (by omega)) hc hr' hp'
  have hlastc := before_trans tr hlastr hrc
  obtain ⟨hinit, hcells⟩ := DuplexRecordAnchor.table_cells p H tr Qtot hcons hQ hold
    s absorbed label data hD (PublicInitFrame.addr pubBytes hL c1) hroot hi n hn
    habs hstep har hdr c hlastc
  have hw := InitialWalkCells.walk_of_cells p pubBytes hlen hL c1 H tr Qtot hcons hQ hold
    T (DuplexPrefixTable.table_consistent H tr hcons c) fuel n hn hle
    s absorbed label data hD hroot habs hstep hinit
    (fun j hj => (hcells j hj).1) (fun j hj => (hcells j hj).2)
  have hrw : StrictReseedDecoder.recover tag T (H (OpeningReseedFrame.addr tag h62 (s n))) =
      some (OpeningReseedFrame.addr tag h62 (s n), s n) := by
    simpa only [← hs] using hrecover
  change (match StrictReseedDecoder.recover tag T
      (H (OpeningReseedFrame.addr tag h62 (s n))) with
    | none => none
    | some (_, endpoint) => InitialWalk.walk p pubBytes T fuel endpoint) = _
  rw [hrw]
  exact hw

#print axioms decode_of_raw
#print axioms raw_before_next
end AspisR1.ReseedPrefix
end
