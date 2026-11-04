import NGD_RowPayload
import NGO_DecodeTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_CallerDomains
/-- All deployed decode_k call shapes, including the three claim writes. -/
inductive Call : Nat → Nat → Nat → Prop where
  | initial : Call 14 1 0
  | round (row : Nat) (low : 15≤row) (high : row≤24) : Call row 28 0
  | claims (p : Nat) (live : p<3) : Call 25 29 (p*29)
  | extra : Call 25 29 87
  | beforeZ1 : Call 26 29 0

theorem numeric (row n off : Nat) (call : Call row n off) :
    14≤row ∧ row<27 ∧ 0<n ∧ off+n≤116 ∧
      32*off+32*n≤NFU_PacketDomains.payloadSize row := by
  cases call <;> simp_all [NFU_PacketDomains.payloadSize] <;> split_ifs <;> omega

/-- These bounds are derived from the original record's header size. They
require no decoder result or canonicality fact. Producer substitution remains
separate until the complete parse_record carrier theorem has been established. -/
theorem record_domain (N off start : Usize)
    (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (call : Call r.row.val N.val off.val)
    (framed : r.framed.val.length=5+NFU_PacketDomains.payloadSize r.row.val)
    (startValue : start.val=32*off.val) :
    NGD_DecodeTrace.Domain N r off start ∧ ¬r.row<14#u8 := by
  obtain ⟨low,high,positive,total,fitting⟩ := numeric r.row.val N.val off.val call
  have cap := NFU_PacketDomains.payload_bound r.row.val
  constructor
  · exact ⟨by omega,by omega,startValue,positive,by omega⟩
  · change ¬r.row.val<14
    omega
#print axioms numeric
#print axioms record_domain
end NGO_CallerDomains
