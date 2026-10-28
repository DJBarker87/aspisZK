import R1Z.PV_RDEA_NameBytes
import R1Z.PV_RDEA_JoinSuccessRequests
import R1Z.PV_RDEA_ProtocolSites
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_ReservationJoin
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint

def isAbsolute : List U8 → Bool
  | [] => false
  | b::_ => decide (b=47#u8)

theorem relative (digest : List (Fin 256)) : isAbsolute (PV_RDEA_NameBytes.bytes digest)=false := by
  have h := PV_RDEA_NameBytes.no_slash digest
  cases hb : PV_RDEA_NameBytes.bytes digest with
  | nil => rfl
  | cons b bs =>
    have hn : b≠47#u8 := by
      intro he
      apply h
      rw [hb,he]
      exact List.mem_cons_self
    simp only [hb,isAbsolute,hn,decide_false]

/-- The absolute/relative branch is derived from the actual encoded bytes,
including when digest bytes depend on witness data. -/
theorem prefix {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat)
    (digest : List (Fin 256)) (length : digest.length=32)
    (base : List U8) (needSep : Bool) (w : World S F) :
    PV_RDEA_PrefixWords.Prefix
      (sizes (sourceJoin (PV_RDEA_CloneExecution.clone step shape address)
        (PV_RDEA_AppendExecution.append step shape)
        (isAbsolute (PV_RDEA_NameBytes.bytes digest)) needSep base (PV_RDEA_NameBytes.bytes digest) w).2.history)
      (sizes w.history++PV_RDEA_ProtocolSites.requestWord .reservation base.length needSep) := by
  have h := PV_RDEA_JoinRequests.join_requests_prefix step shape width address
    (isAbsolute (PV_RDEA_NameBytes.bytes digest)) needSep base (PV_RDEA_NameBytes.bytes digest) w
  rw [relative,PV_RDEA_NameBytes.byte_length,length] at h
  exact h

#print axioms relative
#print axioms prefix
end R1Z.PV_RDEA_ReservationJoin
