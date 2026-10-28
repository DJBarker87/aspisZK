import R1Z.PV_Join_PublicCarrierBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_PublicOp20
open Aeneas Aeneas.Std Result ProverRwFull
abbrev NativeAfter := PV_CB_Op229Transport.After
abbrev CB3After := PV_CB3_ShippedOp229.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
def encode (x : NativeAfter) : CB3After := ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
def decode (x : CB3After) : NativeAfter := ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
theorem native_roundtrip (x : NativeAfter) : decode (encode x) = x := by cases x; rfl
theorem cb3_roundtrip (x : CB3After) : encode (decode x) = x := by cases x; rfl
/-- The two op20 choices are nominal carriers related by this explicit bijection.
No equality of their whole ExternalTypes dictionaries is asserted. -/
def carrier (base : ExternalTypes) :
    @ExternalTypes.op20 (PV_CB_Op229Transport.native base) ≃
      @ExternalTypes.op20 (PV_CB3_Afterstate.selectedTypes base) :=
  ⟨encode,decode,native_roundtrip,cb3_roundtrip⟩

theorem selected_source (base : ExternalTypes)
    (left : @ExternalFuns (PV_CB_Op229Transport.native base))
    (right : @ExternalFuns (PV_CB3_Afterstate.selectedTypes base))
    (a b : PV_CB_Op229Transport.Late base) :
    @ExternalFuns.op229 (PV_CB_Op229Transport.native base)
      (PV_Join_PublicInstall.selected base left) a b =
    @ExternalFuns.op229 (PV_CB3_Afterstate.selectedTypes base)
      (PV_CB3_Op229Source.selected base right)
      (PV_Join_PublicCarrierBridge.encode base a) (PV_Join_PublicCarrierBridge.encode base b) := by
  rw [PV_Join_PublicInstall.source,PV_CB3_Op229Source.op229_source]
  exact PV_Join_PublicCarrierBridge.source base a b
#print axioms native_roundtrip
#print axioms cb3_roundtrip
#print axioms carrier
#print axioms selected_source
end R1Z.PV_Join_PublicOp20
