import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_EndpointCounter
open PV_OWN_Link
abbrev Counts := Nat → Nat
inductive Error where
 | endpointCapacity (row : UInt16)
 deriving DecidableEq
/-- A source-level scalar counter model. It does not assume a native stack-array
carrier or hide its initialization/store obligation. -/
def bump (counts : Counts) (row : UInt16) : Except Error Counts :=
 if row.toNat≥1024 ∨ counts row.toNat≥2 then .error (.endpointCapacity row)
 else .ok (fun i=>if i=row.toNat then counts i+1 else counts i)
/-- Source has separate producer and consumer arrays, not one merged counter. -/
def check : List Link → Counts → Counts → Except Error (Counts × Counts)
 | [],producers,consumers => .ok (producers,consumers)
 | v::vs,producers,consumers => do
  let producers←bump producers v.producer
  let consumers←bump consumers v.consumer
  check vs producers consumers
attribute [local irreducible] bump check
end R1Z.PV_OWND_EndpointCounter
