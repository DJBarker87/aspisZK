import R1Z.PV_RDEA_ReservationJoin
import R1Z.PV_CBL_StringBytesAdapter
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_LiteralSites
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint

inductive Site where
  | recovery | ledger | proof | statement

def protocol : Site → PV_RDEA_ProtocolSites.Site
  | .recovery => .noteRecovery
  | .ledger => .maskNonceLedger
  | .proof => .proof
  | .statement => .statement

def text : Site → String
  | .recovery => "note-recovery.json"
  | .ledger => "mask-nonce-ledger"
  | .proof => "proof.bin"
  | .statement => "statement.bin"

def bytes (site : Site) : List U8 := PV_CBL_StringBytesAdapter.encodeList (text site)

theorem length (site : Site) : (bytes site).length=PV_RDEA_ProtocolSites.argumentLength (protocol site) := by
  cases site <;> rfl

theorem relative (site : Site) : PV_RDEA_ReservationJoin.isAbsolute (bytes site)=false := by
  cases site <;> decide

/-- Four mechanically identified client literal calls, with both the byte
length and Unix branch derived from each source spelling. -/
theorem request_prefix {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat)
    (site : Site) (base : List U8) (needSep : Bool) (w : World S F) :
    PV_RDEA_PrefixWords.Prefix
      (sizes (sourceJoin (PV_RDEA_CloneExecution.clone step shape address)
        (PV_RDEA_AppendExecution.append step shape)
        (PV_RDEA_ReservationJoin.isAbsolute (bytes site)) needSep base (bytes site) w).2.history)
      (sizes w.history++PV_RDEA_ProtocolSites.requestWord (protocol site) base.length needSep) := by
  have h := PV_RDEA_JoinRequests.join_requests_prefix step shape width address
    (PV_RDEA_ReservationJoin.isAbsolute (bytes site)) needSep base (bytes site) w
  rw [relative,length] at h
  simpa only [relative,PV_RDEA_ProtocolSites.requestWord] using h

#print axioms length
#print axioms relative
#print axioms request_prefix
end R1Z.PV_RDEA_LiteralSites
