import R1UnifiedSemanticRecovery
import R1OpeningPrefixCompletion
import TraceAppend

/-! Extending a trace after an already-read address does not change the
functional table snapshot before that address, hence does not change either
typed prefix parser's result at that cut. -/
set_option autoImplicit false
namespace AspisR1.TypedPrefixExtension

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SourceDuplexStep
open AspisV8R19.DuplexFrames

variable {M Cv : Type} {L : Nat}

theorem semantic_typed_append_eq (p : Params M Cv L) (pubBytes : Bytes)
    (t : Table (Addr L) State) (tr tail : List (Addr L × State))
    (a : Addr L) (ha : a ∈ tr.map Prod.fst) (fuel : Nat) (endpoint : State) :
    UnifiedSemanticRecovery.typed p pubBytes
        (tableBefore t (tr ++ tail) a) fuel endpoint =
      UnifiedSemanticRecovery.typed p pubBytes
        (tableBefore t tr a) fuel endpoint := by
  rw [TraceAppend.tableBefore_append t tr tail a ha]

theorem opening_typed_append_eq (p : Params M Cv L) (pubBytes : Bytes)
    (tag : Byte) (t : Table (Addr L) State) (tr tail : List (Addr L × State))
    (a : Addr L) (ha : a ∈ tr.map Prod.fst) (semanticFuel openingFuel : Nat)
    (endpoint : State) :
    OpeningPrefixCompletion.typed p pubBytes tag
        (tableBefore t (tr ++ tail) a) semanticFuel openingFuel endpoint =
      OpeningPrefixCompletion.typed p pubBytes tag
        (tableBefore t tr a) semanticFuel openingFuel endpoint := by
  rw [TraceAppend.tableBefore_append t tr tail a ha]

#print axioms semantic_typed_append_eq
#print axioms opening_typed_append_eq
end AspisR1.TypedPrefixExtension
