import NCB_DigestTotal
import NBL_MaterialTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCD_ChronologicalQuery
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
abbrev Bytes32 := Array U8 32#usize
/-- Exact same causal replies from the native observer. The value law is the
existing runtime SHA realization row, not a new cryptographic assumption. -/
def pairs {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (hash : Hash) (reply : Nat → Bytes32)
    (reads : ∀ i, i<8 → decodeState (reply (2*i+1))=
      H (flatten (NBA_Transcript.readParts (reply (2*i)) 1#u8)))
    (advances : ∀ i, i<8 → decodeState (reply (2*i+2))=
      H (flatten (NBA_Transcript.readParts (reply (2*i)) 2#u8))) :
    NBL_MaterialTrace.Trace (F3U_Rehash.dictionary H D) hash (reply 0) := by
  let p0 : NBL_MaterialTrace.Pair (F3U_Rehash.dictionary H D) hash (reply 0) :=
    ⟨reply 1,reply 2,
     NCB_DigestTotal.reached H D hash _ _ (reads 0 (by decide)),
     NCB_DigestTotal.reached H D hash _ _ (advances 0 (by decide))⟩
  let p1 : NBL_MaterialTrace.Pair (F3U_Rehash.dictionary H D) hash (reply 2) :=
    ⟨reply 3,reply 4,
     NCB_DigestTotal.reached H D hash _ _ (reads 1 (by decide)),
     NCB_DigestTotal.reached H D hash _ _ (advances 1 (by decide))⟩
  let p2 : NBL_MaterialTrace.Pair (F3U_Rehash.dictionary H D) hash (reply 4) :=
    ⟨reply 5,reply 6,
     NCB_DigestTotal.reached H D hash _ _ (reads 2 (by decide)),
     NCB_DigestTotal.reached H D hash _ _ (advances 2 (by decide))⟩
  let p3 : NBL_MaterialTrace.Pair (F3U_Rehash.dictionary H D) hash (reply 6) :=
    ⟨reply 7,reply 8,
     NCB_DigestTotal.reached H D hash _ _ (reads 3 (by decide)),
     NCB_DigestTotal.reached H D hash _ _ (advances 3 (by decide))⟩
  let p4 : NBL_MaterialTrace.Pair (F3U_Rehash.dictionary H D) hash (reply 8) :=
    ⟨reply 9,reply 10,
     NCB_DigestTotal.reached H D hash _ _ (reads 4 (by decide)),
     NCB_DigestTotal.reached H D hash _ _ (advances 4 (by decide))⟩
  let p5 : NBL_MaterialTrace.Pair (F3U_Rehash.dictionary H D) hash (reply 10) :=
    ⟨reply 11,reply 12,
     NCB_DigestTotal.reached H D hash _ _ (reads 5 (by decide)),
     NCB_DigestTotal.reached H D hash _ _ (advances 5 (by decide))⟩
  let p6 : NBL_MaterialTrace.Pair (F3U_Rehash.dictionary H D) hash (reply 12) :=
    ⟨reply 13,reply 14,
     NCB_DigestTotal.reached H D hash _ _ (reads 6 (by decide)),
     NCB_DigestTotal.reached H D hash _ _ (advances 6 (by decide))⟩
  let p7 : NBL_MaterialTrace.Pair (F3U_Rehash.dictionary H D) hash (reply 14) :=
    ⟨reply 15,reply 16,
     NCB_DigestTotal.reached H D hash _ _ (reads 7 (by decide)),
     NCB_DigestTotal.reached H D hash _ _ (advances 7 (by decide))⟩
  exact ⟨p0,p1,p2,p3,p4,p5,p6,p7⟩

theorem materialized {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (hash : Hash) (reply : Nat → Bytes32)
    (reads : ∀ i, i<8 → decodeState (reply (2*i+1))=
      H (flatten (NBA_Transcript.readParts (reply (2*i)) 1#u8)))
    (advances : ∀ i, i<8 → decodeState (reply (2*i+2))=
      H (flatten (NBA_Transcript.readParts (reply (2*i)) 2#u8))) :
    let trace := pairs H D hash reply reads advances
    NBA_QueryFactor.materialize (F3U_Rehash.dictionary H D) hash (reply 0)=
      ok (trace.blocks,trace.advances) :=
  NBL_MaterialTrace.source _ hash _ (pairs H D hash reply reads advances)

#print axioms materialized
end AspisR1.NCD_ChronologicalQuery
end
