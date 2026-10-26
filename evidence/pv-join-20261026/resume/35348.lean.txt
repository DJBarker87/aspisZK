import R1Z.PDict_StatementTypesSource
import R1Z.PV_CB3_Afterstate
set_option autoImplicit false
namespace R1Z.PV_Join_Op20Value
open Aeneas Aeneas.Std
abbrev NativeAfter := PDict_StatementTypes.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev CB3After := PV_CB3_ShippedOp229.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

def encode (x : NativeAfter) : CB3After := ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
def decode (x : CB3After) : NativeAfter := ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
theorem native_roundtrip (x : NativeAfter) : decode (encode x) = x := by cases x; rfl
theorem cb3_roundtrip (x : CB3After) : encode (decode x) = x := by cases x; rfl
/-- The concrete op20 value carriers are bijective; no equality of complete
ExternalTypes or ExternalFuns dictionaries is inferred. -/
def carrier : NativeAfter ≃ CB3After := ⟨encode,decode,native_roundtrip,cb3_roundtrip⟩
theorem components (x : NativeAfter) :
    (encode x).next_pair_index = x.next_pair_index ∧
    (encode x).next_root = x.next_root ∧
    (encode x).next_frontier = x.next_frontier := ⟨rfl,rfl,rfl⟩
#print axioms native_roundtrip
#print axioms cb3_roundtrip
#print axioms carrier
#print axioms components
end R1Z.PV_Join_Op20Value
