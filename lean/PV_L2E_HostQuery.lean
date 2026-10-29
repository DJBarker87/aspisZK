import PV_L2D_QueryBounds
set_option autoImplicit false
namespace PV_L2E_HostQuery
open PV_L2D_QueryScan PV_L2D_QueryBounds

inductive Result where
  | ok (queries : List Nat) (advance : Nat)
  | exhausted
  | missingWord
  deriving DecidableEq, Repr

inductive Event where
  | drawGuard (stop : Bool)
  | acceptedGuard (stop : Bool)
  | compare (index : Nat) (equal : Bool)
  | readByte (block offset : Nat)
  | writeQuery (index : Nat)
  | selectAdvance (index : Nat)
  deriving DecidableEq, Repr

def comparisons : PV_L2D_QueryScan.Event → List Event
  | .compare i b => [.compare i b]
  | _ => []

/-- Flattened candidate list, in increasing draw order. The bytes-to-words
binding is separate. This preserves the HOST guard order, which is different
from core::QueryScan and must not be obtained by equality of stop bits. -/
def run (s : State) (words : List Nat) : Result × List Event :=
  if s.draws=64 then
    if s.accepted.length=22 then
      (.ok s.accepted 7,[.drawGuard true,.acceptedGuard true,.selectAdvance 7])
    else (.exhausted,[.drawGuard true,.acceptedGuard false])
  else if s.accepted.length=22 then
    (.ok s.accepted (s.draws/8),
      [.drawGuard false,.acceptedGuard true,.selectAdvance (s.draws/8)])
  else match words with
    | [] => (.missingWord,[.drawGuard false,.acceptedGuard false])
    | x::xs =>
      let m := member x 0 s.accepted
      let after := next s x
      let tail := run after xs
      (tail.1,[.drawGuard false,.acceptedGuard false] ++
        [.readByte (s.draws/8) (4*(s.draws%8)),
         .readByte (s.draws/8) (4*(s.draws%8)+1),
         .readByte (s.draws/8) (4*(s.draws%8)+2),
         .readByte (s.draws/8) (4*(s.draws%8)+3)] ++
        m.2.flatMap comparisons ++
        (if m.1 then [] else [.writeQuery s.accepted.length]) ++ tail.2)
termination_by words.length

theorem at_cap (s : State) (words : List Nat) (hd : s.draws=64) :
    run s words = if s.accepted.length=22 then
      (.ok s.accepted 7,[.drawGuard true,.acceptedGuard true,.selectAdvance 7])
      else (.exhausted,[.drawGuard true,.acceptedGuard false]) := by
  rw [run,if_pos hd]

theorem complete (s : State) (words : List Nat) (hd : s.draws≠64)
    (ha : s.accepted.length=22) :
    run s words=(.ok s.accepted (s.draws/8),
      [.drawGuard false,.acceptedGuard true,.selectAdvance (s.draws/8)]) := by
  rw [run,if_neg hd,if_pos ha]

theorem read_safe (s : State) (admitted : Admitted s) (live : stopped s=false) :
    s.draws/8<8 ∧ ∀ i : Nat, i<4 → 4*(s.draws%8)+i<32 := by
  have hdraw := admitted.2.2.2.1
  have hn : s.draws≠64 := by
    intro he
    simp [stopped,he] at live
  have hl : s.draws<64 := by omega
  have hm := Nat.mod_lt s.draws (by decide : 0<8)
  constructor
  · omega
  · intros; omega

/-- The first host guard selects 7 at draw 64; dividing 64 by 8 is never
used to index the advance array. This includes completion at the final word. -/
theorem no_eighth_advance (s : State) (words : List Nat)
    (hd : s.draws=64) (ha : s.accepted.length=22) :
    (run s words).1=.ok s.accepted 7 := by rw [at_cap s words hd,if_pos ha]

#print axioms at_cap
#print axioms complete
#print axioms read_safe
#print axioms no_eighth_advance
end PV_L2E_HostQuery
