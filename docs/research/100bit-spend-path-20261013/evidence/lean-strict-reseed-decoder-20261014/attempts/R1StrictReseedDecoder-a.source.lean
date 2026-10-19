import R1PrefixedStateCodec
import R1ReseedBoundary

/-! Parse only the exact fixed P3 domain/tag prefix and recover its trailing
state. The table lookup and source-read assumptions remain those of the
existing reseed boundary theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.StrictReseedDecoder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

def parse (tag : Byte) (a : Addr L) : Option State :=
  PrefixedStateCodec.parse (OpeningReseedFrame.domain ++ [tag]) a

theorem parse_addr (tag : Byte) (hL : 62 ≤ L) (s : State) :
    parse tag (OpeningReseedFrame.addr tag hL s) = some s := by
  change PrefixedStateCodec.parse (OpeningReseedFrame.domain ++ [tag])
      (TrailingStateFrame.frameAddr (OpeningReseedFrame.domain ++ [tag]) s _) = some s
  exact PrefixedStateCodec.parse_frameAddr _ _ _

theorem parse_sound (tag : Byte) (a : Addr L) (s : State)
    (hparse : parse tag a = some s) :
    a.toBytes = OpeningReseedFrame.domain ++ [tag] ++ bytes s := by
  have h := PrefixedStateCodec.parse_sound
    (OpeningReseedFrame.domain ++ [tag]) a s hparse
  simpa [parse, List.append_assoc] using h

def recover (tag : Byte) (T : Table (Addr L) State) (endpoint : State) :
    Option (Addr L × State) :=
  match ReseedBoundary.findCell T endpoint with
  | none => none
  | some a => (parse tag a).map fun s => (a, s)

theorem recover_of_cell (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (T : Table (Addr L) State)
    (hT : ∀ b v, T b = some v → v = H b ∧ Read tr b)
    (tag : Byte) (hL : 62 ≤ L) (s : State)
    (hcell : T (OpeningReseedFrame.addr tag hL s) =
      some (H (OpeningReseedFrame.addr tag hL s))) :
    recover tag T (H (OpeningReseedFrame.addr tag hL s)) =
      some (OpeningReseedFrame.addr tag hL s, s) := by
  have hfind := ReseedBoundary.findCell_correct p H tr Qtot hcons hQ hcoll
    T hT (OpeningReseedFrame.addr tag hL s) hcell
  simp [recover, hfind, parse_addr]

#print axioms parse_addr
#print axioms parse_sound
#print axioms recover_of_cell

end AspisR1.StrictReseedDecoder
end
