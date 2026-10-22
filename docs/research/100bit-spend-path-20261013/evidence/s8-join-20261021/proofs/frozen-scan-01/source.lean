import S8JoinCompactTotal
import OraclePortFrozenOrderDecision

/-! The actual compact::check_values call scans y1 at offsets 7031..7495.
Its reference result is derived from the same stored bytes accepted by the
frozen decision. This is not a proof of the surrounding source parser. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinFrozenScan
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft S8JoinCompactChunks S8JoinCompactTotal
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)

def segment (b : Slice U8) (offset size : Nat) : Slice U8 :=
  ⟨(b.val.drop offset).take size,by
    simp only [List.length_take,List.length_drop]
    exact (Nat.min_le_right _ _).trans ((Nat.sub_le _ _).trans b.property)⟩

theorem segment_wire (b : Slice U8) (offset size : Nat) :
    wire (segment b offset size) = slice (wire b) offset size := by
  simp only [wire,segment,slice,List.map_take,List.map_drop]

theorem parse_scan (b : Bytes) (p : Parsed) (parsed : parse b = some p) : scan b := by
  unfold parse at parsed
  split at parsed
  · contradiction
  · split at parsed
    · contradiction
    · assumption

theorem parsed_y1 (stored : Slice U8) (tr : ErasedPrefix) (p : Parsed)
    (parsed : OraclePortStoredParserC4.parseReached (wire stored) tr = some p) :
    S8OwnedP6.check_values_owned (segment stored 7031 464) = .ok (.Ok ()) := by
  have hp := (OraclePortStoredParserC4.parsed _ _ _ parsed).1
  have length := ((OraclePortHeader.accepts_iff _).mp (parse_header _ _ hp).1).1
  have good := (parse_scan _ _ hp).1
  have slen : (segment stored 7031 464).val.length = 464 := by
    have hlen : stored.val.length = 57607 := by simpa only [wire,List.length_map] using length
    simp only [segment,List.length_take,List.length_drop,hlen]
    decide
  have run := aligned_scan_total (segment stored 7031 464) (by rw [slen]; decide)
  simpa only [segment_wire,if_pos good] using run

/-- No congruence, successful decoder, or free S8 premise: the exact y1 scan
result follows from acceptance of dV_frozen on these same bytes. -/
theorem accepted_y1 (stored : Slice U8) (tr : ErasedPrefix) (m : ErasedMessage)
    (H : Bytes → State)
    (accepted : (eval H (OraclePortFrozenOrder.dV_frozen (wire stored) tr m)).2 = true) :
    S8OwnedP6.check_values_owned (segment stored 7031 464) = .ok (.Ok ()) := by
  obtain ⟨_,p,q,hp,_,_,_⟩ := OraclePortFrozenOrder.accepted _ _ _ H accepted
  exact parsed_y1 stored tr p hp

#print axioms segment_wire
#print axioms parse_scan
#print axioms parsed_y1
#print axioms accepted_y1
end AspisR1.S8JoinFrozenScan
end
